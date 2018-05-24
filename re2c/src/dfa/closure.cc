#include <assert.h>
#include "src/util/c99_stdint.h"
#include <stdlib.h>
#include <string.h>
#include <algorithm>
#include <set>
#include <stack>
#include <utility>
#include <valarray>

#include "src/conf/opt.h"
#include "src/dfa/closure.h"
#include "src/dfa/dfa.h"
#include "src/dfa/tagpool.h"
#include "src/dfa/tcmd.h"
#include "src/nfa/nfa.h"
#include "src/re/rule.h"

namespace re2c
{

static void closure_posix(const closure_t &init, closure_t &done, closure_t *shadow, Tagpool &tagpool, const std::vector<Tag> &tags, const bmatrix_t *bmatrix, size_t noldclos);
static void closure_leftmost(const closure_t &init, closure_t &done, closure_t *shadow, Tagpool &tagpool);
static void prune(closure_t &clos, std::valarray<Rule> &rules);
static void lower_lookahead_to_transition(closure_t &clos);
static tcmd_t *generate_versions(dfa_t &dfa, closure_t &clos, Tagpool &tagpool, newvers_t &newvers);
static void orders(closure_t &clos, Tagpool &tagpool, const std::vector<Tag> &tags,
	const bmatrix_t *bmatrix, bmatrix_t *&bmatrix1, size_t noldclos);
static bool cmpby_rule_state(const clos_t &x, const clos_t &y);

tcmd_t *closure(dfa_t &dfa, closure_t &clos1, closure_t &clos2,
	Tagpool &tagpool, newvers_t &newvers, closure_t *shadow,
	const bmatrix_t *bmatrix, bmatrix_t *&bmatrix1, size_t noldclos)
{
	// build tagged epsilon-closure of the given set of NFA states
	if (tagpool.opts->posix_captures) {
		closure_posix(clos1, clos2, shadow, tagpool, dfa.tags, bmatrix, noldclos);
		prune(clos2, dfa.rules);
		std::sort(clos2.begin(), clos2.end(), cmpby_rule_state);
		orders(clos2, tagpool, dfa.tags, bmatrix, bmatrix1, noldclos);
	} else {
		closure_leftmost(clos1, clos2, shadow, tagpool);
		prune(clos2, dfa.rules);
	}

	// see note [the difference between TDFA(0) and TDFA(1)]
	if (!tagpool.opts->lookahead) {
		lower_lookahead_to_transition(clos2);
		if (shadow) lower_lookahead_to_transition(*shadow);
	}

	// merge tags from different rules, find nondeterministic tags
	tcmd_t *cmd = generate_versions(dfa, clos2, tagpool, newvers);
	if (shadow) generate_versions(dfa, *shadow, tagpool, newvers);

	return cmd;
}

bool cmpby_rule_state(const clos_t &x, const clos_t &y)
{
	const nfa_state_t *sx = x.state, *sy = y.state;
	const size_t rx = sx->rule, ry = sy->rule;
	if (rx < ry) return true;
	if (rx > ry) return false;
	if (sx < sy) return true;
	if (sx > sy) return false;
	// all items in closute have different states
	return false;
}


/* note [epsilon-closures in tagged NFA]
 *
 * The closure includes all NFA states that are reachable by epsilon-paths
 * from the given set of states and either are final or have non-epsilon
 * transitions. Note that by construction NFA states cannot have both
 * epsilon and non-epsilon transitions.
 *
 * Each closure state might be reachable by multiple epsilon-paths with
 * different tags: this means that the regular expression is ambiguous
 * and can be parsed in different ways. Which parse to choose depends on the
 * disambiguation policy. RE2C supports two policies: leftmost greedy and
 * POSIX.
 *
 * We use Goldber-Radzik algorithm to find the "shortest path".
 * Both disambiguation policies forbid epsilon-cycles with negative weight.
 */

static void enqueue(clos_t x, std::stack<nfa_state_t*> &bstack, closure_t &done,
	closure_t *shadow, Tagpool &tagpool, const std::vector<Tag> &tags,
	const bmatrix_t *bmatrix, size_t noldclos)
{
	nfa_state_t *n = x.state;
	uint32_t &i = n->clos;

	if (i == NOCLOS) {
		i = static_cast<uint32_t>(done.size());
		done.push_back(x);
	} else {
		clos_t &y = done[i];
		int h1, h2, l;
		l = tagpool.history.precedence (x, y, h1, h2, bmatrix, tags, noldclos);
		if (l < 0) std::swap(x, y);
		if (shadow && l != 0) shadow->push_back(x);
		if (l >= 0) return;
	}

	if (n->status != GOR_TOPSORT) {
		bstack.push(n);
		n->status = GOR_NEWPASS;
	}
}

static void scan(nfa_state_t *n, std::stack<nfa_state_t*> &bstack, closure_t &done,
	closure_t *shadow, Tagpool &tagpool, const std::vector<Tag> &tags,
	const bmatrix_t *bmatrix, size_t noldclos)
{
	tagtree_t &history = tagpool.history;
	clos_t x = done[n->clos];
	switch (n->type) {
		case nfa_state_t::NIL:
			x.state = n->nil.out;
			enqueue(x, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
			break;
		case nfa_state_t::ALT:
			x.state = n->alt.out2;
			enqueue(x, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
			x.state = n->alt.out1;
			enqueue(x, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
			break;
		case nfa_state_t::TAG:
			x.state = n->tag.out;
			x.tlook = history.push(x.tlook, n->tag.info,
				n->tag.bottom ? TAGVER_BOTTOM : TAGVER_CURSOR);
			enqueue(x, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
			break;
		case nfa_state_t::RAN:
		case nfa_state_t::FIN:
			break;
	}
}

void closure_posix(const closure_t &init, closure_t &done,
	closure_t *shadow, Tagpool &tagpool, const std::vector<Tag> &tags,
	const bmatrix_t *bmatrix, size_t noldclos)
{
	std::stack<nfa_state_t*>
		&astack = tagpool.astack,
		&bstack = tagpool.bstack;

	// enqueue all initial states
	done.clear();
	if (shadow) shadow->clear();
	for (cclositer_t c = init.begin(); c != init.end(); ++c) {
		enqueue(*c, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
	}

	// Gordberg-Radzik 'shortest path' algorithm.
	// Papers: 1993, "A heuristic improvement of the Bellman-Ford
	// algorithm" by Goldberg, Radzik and 1996, Shortest paths algorithms:
	// Theory andexperimental evaluation" by Cherkassky, Goldberg, Radzik.
	// Complexity for digraph G=(V,E) is O(|V|*|E|).
	for (; !bstack.empty(); ) {

		// 1st step: find admissible subgraph reachable from B-stack
		// and topologically sort it (this can be done by a single
		// depth-first search that scans each state and pushes traversed
		// states to A-stack in postorder)
		for (; !bstack.empty(); ) {
			nfa_state_t *n = bstack.top();
			if (n->status == GOR_NEWPASS) {
				n->status = GOR_TOPSORT;
				scan(n, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
			} else if (n->status == GOR_TOPSORT) {
				bstack.pop();
				astack.push(n);
			} else { // GOR_OFFSTACK
				bstack.pop();
			}
		}

		// 2nd step: scan topologically ordered states from A-stack
		// and push head states of relaxed transitions to B-stack
		for (; !astack.empty(); ) {
			nfa_state_t *n = astack.top();
			astack.pop();
			scan(n, bstack, done, shadow, tagpool, tags, bmatrix, noldclos);
			n->status = GOR_OFFSTACK;
		}
	}

	// reset associated closure items and check status
	// (do this before removing any states from closure)
	for (clositer_t i = done.begin(); i != done.end(); ++i) {
		i->state->clos = NOCLOS;
		assert(i->state->status == GOR_OFFSTACK);
	}
}

/* note [at most one final item per closure]
 *
 * By construction NFA has exactly one final state per rule. Thus closure
 * has at most one final item per rule (in other words, all final items
 * in closure belong to different rules). The rule with the highest priority
 * shadowes all other rules. Final items that correspond to shadowed rules
 * are useless and should be removed as early as possible.
 *
 * If we let such items remain in closure, they may prevent the new DFA
 * state from being merged with other states. This won't affect the final
 * program: meaningless finalizing tags will be removed by dead code
 * elimination and subsequent minimization will merge equivalent final
 * states. However, it's better not to add useless final items at all.
 *
 * Note that the first final item reached by the epsilon-closure it the one
 * with the highest priority (see note [closure items are sorted by rule]).
 */

void closure_leftmost(const closure_t &init, closure_t &done,
	closure_t *shadow, Tagpool &tagpool)
{
	std::stack<clos_t> &todo = tagpool.cstack;

	// enqueue all initial states
	done.clear();
	if (shadow) shadow->clear();
	for (rcclositer_t c = init.rbegin(); c != init.rend(); ++c) {
		todo.push(*c);
	}

	// DFS; linear complexity
	for (; !todo.empty(); ) {
		clos_t x = todo.top();
		todo.pop();
		nfa_state_t *n = x.state;

		if (n->clos == NOCLOS) {
			n->clos = static_cast<uint32_t>(done.size());
			done.push_back(x);
		} else {
			if (shadow) shadow->push_back(x);
			continue;
		}

		switch (n->type) {
			case nfa_state_t::NIL:
				x.state = n->nil.out;
				todo.push(x);
				break;
			case nfa_state_t::ALT:
				x.state = n->alt.out2;
				todo.push(x);
				x.state = n->alt.out1;
				todo.push(x);
				break;
			case nfa_state_t::TAG:
				x.state = n->tag.out;
				x.tlook = tagpool.history.push(x.tlook, n->tag.info,
					n->tag.bottom ? TAGVER_BOTTOM : TAGVER_CURSOR);
				todo.push(x);
				break;
			case nfa_state_t::RAN:
			case nfa_state_t::FIN:
				break;
		}
	}

	// reset associated closure items 
	// (do this before removing any states from closure)
	for (clositer_t i = done.begin(); i != done.end(); ++i) {
		i->state->clos = NOCLOS;
	}
}

void prune(closure_t &clos, std::valarray<Rule> &rules)
{
	clositer_t b = clos.begin(), e = clos.end(), i, j;

	// drop "inner" states (non-final without outgoing non-epsilon transitions)
	j = std::stable_partition(b, e, clos_t::ran);
	e = std::stable_partition(j, e, clos_t::fin);
	size_t n = static_cast<size_t>(e - b);

	// drop all final states except one; mark dropped rules as shadowed
	// see note [at most one final item per closure]
	if (j != e) {
		std::sort(j, e, cmpby_rule_state);
		const uint32_t l = rules[j->state->rule].code->fline;
		for (i = j; ++i < e;) {
			rules[i->state->rule].shadow.insert(l);
		}
		n = static_cast<size_t>(j - b) + 1;
	}

	clos.resize(n);
}

/* note [the difference between TDFA(0) and TDFA(1)]
 *
 * TDFA(0) performs epsilon-closure after transition on symbol,
 * while TDFA(1) performs it before the transition and uses the lookahead
 * symbol to filter the closure.
 *
 * TDFA(0) is one step ahead of TDFA(1): it consumes a symol, then builds
 * epsilon-closure, eagerly applies all tags reachable by it and goes to
 * the next state.
 *
 * TDFA(1) is more lazy: it builds epsilon-closure, then filters it with
 * respect to the current symbol (uses only those states which have outgoing
 * transitions on this symbol), then applies corresponding tags (probably
 * not all tags applied by TDFA(0)) and then consumes the symbol and goes
 * to the next state.
 *
 * Thus in general TDFA(1) raises less conflicts than TDFA(0).
 */

void lower_lookahead_to_transition(closure_t &clos)
{
	for (clositer_t c = clos.begin(); c != clos.end(); ++c) {
		c->ttran = c->tlook;
		c->tlook = HROOT;
	}
}

tcmd_t *generate_versions(dfa_t &dfa, closure_t &clos, Tagpool &tagpool, newvers_t &newvers)
{
	tcmd_t *cmd = NULL;
	const size_t ntag = tagpool.ntags;
	tagver_t *vers = tagpool.buffer, &maxver = dfa.maxtagver;
	tagtree_t &tagtree = tagpool.history;
	const std::vector<Tag> &tags = dfa.tags;
	clositer_t b = clos.begin(), e = clos.end(), c;
	newver_cmp_t cmp = {tagtree};
	newvers_t newacts(cmp);

	// for each tag, if there is at least one tagged transition,
	// allocate new version (negative for bottom and positive for
	// normal transition, however absolute value should be unique
	// among all versions of all tags)
	for (c = b; c != e; ++c) {
		const hidx_t l = c->tlook, h = c->ttran;
		if (h == HROOT) continue;

		const tagver_t *vs = tagpool[c->tvers];
		for (size_t t = 0; t < ntag; ++t) {
			const Tag &tag = tags[t];
			const tagver_t
				h0 = tagtree.last(h, t),
				l0 = tagtree.last(l, t);

			if (h0 == TAGVER_ZERO) continue;

			const tagver_t v = history(tag) ? vs[t] : TAGVER_ZERO;
			newver_t x = {t, v, h};
			const tagver_t
				n = (maxver + 1) * (h0 == TAGVER_BOTTOM ? -1 : 1),
				m = newvers.insert(std::make_pair(x, n)).first->second;
			if (n == m) ++maxver;

			if (!fixed(tag) && (l0 == TAGVER_ZERO || history(tag))) {
				newacts.insert(std::make_pair(x, m));
			}
		}
	}

	// actions
	for (newvers_t::iterator i = newacts.begin(); i != newacts.end(); ++i) {
		const tagver_t m = i->second, v = i->first.base;
		const hidx_t h = i->first.history;
		const size_t t = i->first.tag;
		if (history(tags[t])) {
			cmd = dfa.tcpool.make_add(cmd, abs(m), abs(v), tagtree, h, t);
		} else {
			cmd = dfa.tcpool.make_set(cmd, abs(m), tagtree.last(h, t));
		}
	}

	// mark tags with history
	for (newvers_t::iterator j = newvers.begin(); j != newvers.end(); ++j) {
		if (history(tags[j->first.tag])) dfa.mtagvers.insert(abs(j->second));
	}

	// update tag versions in closure
	for (c = b; c != e; ++c) {
		const hidx_t h = c->ttran;
		if (h == HROOT) continue;

		const tagver_t *vs = tagpool[c->tvers];
		for (size_t t = 0; t < ntag; ++t) {
			const tagver_t
				v0 = vs[t],
				h0 = tagtree.last(h, t),
				v = history(tags[t]) ? v0 : TAGVER_ZERO;
			if (h0 == TAGVER_ZERO) {
				vers[t] = v0;
			} else {
				newver_t x = {t, v, h};
				vers[t] = newvers[x];
			}
		}
		c->tvers = tagpool.insert(vers);
	}

	return cmd;
}

static inline int32_t pack(int32_t longest, int32_t leftmost)
{
	// leftmost: higher 2 bits, longest: lower 30 bits
	return longest | (leftmost << 30);
}

void orders(closure_t &clos, Tagpool &tagpool, const std::vector<Tag> &tags,
	const bmatrix_t *bmatrix, bmatrix_t *&bmatrix1, size_t noldclos)
{
	const size_t nclos = clos.size();
	bmatrix1 = tagpool.alc.alloct<bmatrix_t>(nclos * nclos);

	for (size_t i = 0; i < nclos; ++i) {
		for (size_t j = i + 1; j < nclos; ++j) {
			int rho1, rho2, l;
			l = tagpool.history.precedence (clos[i], clos[j], rho1, rho2, bmatrix, tags, noldclos);
			bmatrix1[i * nclos + j] = pack(rho1, l);
			bmatrix1[j * nclos + i] = pack(rho2, -l);
		}
		bmatrix1[i * nclos + i] = 0;
		clos[i].index = i;
	}
}

} // namespace re2c
