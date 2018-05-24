#include <assert.h>
#include <stdlib.h>

#include "src/dfa/closure.h"
#include "src/dfa/tagtree.h"

namespace re2c
{

static const tagver_t DELIM = TAGVER_CURSOR - 1;

tagtree_t::tagtree_t(): nodes(), path1(), path2() {}

tagver_t tagtree_t::elem(hidx_t i) const { return nodes[i].elem; }

hidx_t tagtree_t::pred(hidx_t i) const { return nodes[i].pred; }

size_t tagtree_t::tag(hidx_t i) const { return nodes[i].tag; }

hidx_t tagtree_t::push(hidx_t i, size_t t, tagver_t v)
{
	node_t x = {i, v, t};
	nodes.push_back(x);
	return static_cast<hidx_t>(nodes.size() - 1);
}

tagver_t tagtree_t::last(hidx_t i, size_t t) const
{
	for (; i != HROOT; i = pred(i)) {
		if (tag(i) == t) return elem(i);
	}
	return TAGVER_ZERO;
}

int32_t tagtree_t::compare_reversed(hidx_t x, hidx_t y, size_t t) const
{
	// compare in reverse, from tail to head: direction makes
	// no difference when comparing for exact coincidence
	for (;;) {
		for (; x != HROOT && tag(x) != t; x = pred(x));
		for (; y != HROOT && tag(y) != t; y = pred(y));
		if (x == HROOT && y == HROOT) return 0;
		if (x == HROOT) return -1;
		if (y == HROOT) return 1;
		if (elem(x) > elem(y)) return -1;
		if (elem(x) < elem(y)) return 1;
		x = pred(x);
		y = pred(y);
	}
}

static int height(ssize_t xtag, const std::vector<Tag> &tags)
{
	const size_t tag = static_cast<size_t>(abs(xtag));
	return tags[tag].height + (tag % 2 == 0 ? 1 : 0);
}

static void reconstruct_history(const tagtree_t &history, std::vector<ssize_t> &path, hidx_t idx)
{
	path.clear();
	for (; idx != HROOT; idx = history.pred(idx)) {
		const ssize_t
			sign = history.elem(idx) < 0 ? -1 : 1,
			xtag = static_cast<ssize_t>(history.tag(idx));
		path.push_back(sign * xtag);
	}
}

static inline int32_t unpack_longest(int32_t value)
{
	// lower 30 bits
	return value & 0x3fffFFFF;
}

static inline int32_t unpack_leftmost(int32_t value)
{
	// higher 2 bits
	return value >> 30u;
}

int tagtree_t::precedence(const clos_t &x, const clos_t &y, int &rhox, int &rhoy,
	const bmatrix_t *bmatrix, const std::vector<Tag> &tags, size_t nclos)
{
	reconstruct_history(*this, path1, x.tlook);
	reconstruct_history(*this, path2, y.tlook);
	std::vector<ssize_t>::const_reverse_iterator
		i1 = path1.rbegin(), e1 = path1.rend(), j1 = i1, g1,
		i2 = path2.rbegin(), e2 = path2.rend(), j2 = i2, g2;
	const size_t xi = x.index, yi = y.index;
	const bool fork_frame = xi == yi;

	// find fork
	if (fork_frame) {
		for (; j1 != e1 && j2 != e2 && *j1 == *j2; ++j1, ++j2);
	}

	// longest precedence
	if (!fork_frame) {
		rhox = unpack_longest(bmatrix[xi * nclos + yi]);
		rhoy = unpack_longest(bmatrix[yi * nclos + xi]);
	} else {
		rhox = rhoy = std::numeric_limits<int>::max();
		if (j1 > i1) rhox = rhoy = height(*(j1 - 1), tags);
	}
	for (g1 = j1; g1 != e1; ++g1) {
		rhox = std::min(rhox, height(*g1, tags));
	}
	for (g2 = j2; g2 != e2; ++g2) {
		rhoy = std::min(rhoy, height(*g2, tags));
	}
	if (rhox > rhoy) return -1;
	if (rhox < rhoy) return 1;

	// leftmost precedence
	if (!fork_frame) {
		return unpack_leftmost(bmatrix[xi * nclos + yi]);
	} else {
		// equal => not less
		if (j1 == e1 && j2 == e2) return 0;
		// shorter => less
		if (j1 == e1) return -1;
		if (j2 == e2) return 1;
		// closing => less
		const ssize_t v1 = *j1, v2 = *j2;
		if (v1 % 2 == 1) return -1;
		if (v2 % 2 == 1) return 1;
		// nonnegative => less
		// (unless both are positive, which is only possible because
		// multiple top-level RE don't have proper negative tags)
		const int invert = v1 > 0 && v2 > 0 ? -1 : 1;
		if (v1 > v2) return invert * -1;
		if (v1 < v2) return invert * 1;
	}
	// unreachable
	assert(false);
	return 0;
}

} // namespace re2c
