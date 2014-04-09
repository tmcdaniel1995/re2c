#include <stdio.h>
#define YYCTYPE unsigned short
bool scan(const YYCTYPE * start, const YYCTYPE * const limit)
{
	__attribute__((unused)) const YYCTYPE * YYMARKER; // silence compiler warnings when YYMARKER is not used
#	define YYCURSOR start
Ps:
	/*!re2c
		re2c:yyfill:enable = 0;
				Ps = [\x28-\x28\x5b-\x5b\x7b-\x7b\u0f3a-\u0f3a\u0f3c-\u0f3c\u169b-\u169b\u201a-\u201a\u201e-\u201e\u2045-\u2045\u207d-\u207d\u208d-\u208d\u2329-\u2329\u2768-\u2768\u276a-\u276a\u276c-\u276c\u276e-\u276e\u2770-\u2770\u2772-\u2772\u2774-\u2774\u27c5-\u27c5\u27e6-\u27e6\u27e8-\u27e8\u27ea-\u27ea\u27ec-\u27ec\u27ee-\u27ee\u2983-\u2983\u2985-\u2985\u2987-\u2987\u2989-\u2989\u298b-\u298b\u298d-\u298d\u298f-\u298f\u2991-\u2991\u2993-\u2993\u2995-\u2995\u2997-\u2997\u29d8-\u29d8\u29da-\u29da\u29fc-\u29fc\u2e22-\u2e22\u2e24-\u2e24\u2e26-\u2e26\u2e28-\u2e28\u3008-\u3008\u300a-\u300a\u300c-\u300c\u300e-\u300e\u3010-\u3010\u3014-\u3014\u3016-\u3016\u3018-\u3018\u301a-\u301a\u301d-\u301d\ufd3e-\ufd3e\ufe17-\ufe17\ufe35-\ufe35\ufe37-\ufe37\ufe39-\ufe39\ufe3b-\ufe3b\ufe3d-\ufe3d\ufe3f-\ufe3f\ufe41-\ufe41\ufe43-\ufe43\ufe47-\ufe47\ufe59-\ufe59\ufe5b-\ufe5b\ufe5d-\ufe5d\uff08-\uff08\uff3b-\uff3b\uff5b-\uff5b\uff5f-\uff5f\uff62-\uff62];
		Ps { goto Ps; }
		[^] { return YYCURSOR == limit; }
	*/
}
static const char buffer_Ps [] = "\x28\x00\x5B\x00\x7B\x00\x3A\x0F\x3C\x0F\x9B\x16\x1A\x20\x1E\x20\x45\x20\x7D\x20\x8D\x20\x29\x23\x68\x27\x6A\x27\x6C\x27\x6E\x27\x70\x27\x72\x27\x74\x27\xC5\x27\xE6\x27\xE8\x27\xEA\x27\xEC\x27\xEE\x27\x83\x29\x85\x29\x87\x29\x89\x29\x8B\x29\x8D\x29\x8F\x29\x91\x29\x93\x29\x95\x29\x97\x29\xD8\x29\xDA\x29\xFC\x29\x22\x2E\x24\x2E\x26\x2E\x28\x2E\x08\x30\x0A\x30\x0C\x30\x0E\x30\x10\x30\x14\x30\x16\x30\x18\x30\x1A\x30\x1D\x30\x3E\xFD\x17\xFE\x35\xFE\x37\xFE\x39\xFE\x3B\xFE\x3D\xFE\x3F\xFE\x41\xFE\x43\xFE\x47\xFE\x59\xFE\x5B\xFE\x5D\xFE\x08\xFF\x3B\xFF\x5B\xFF\x5F\xFF\x62\xFF\x00\x00";
int main ()
{
	if (!scan (reinterpret_cast<const YYCTYPE *> (buffer_Ps), reinterpret_cast<const YYCTYPE *> (buffer_Ps + sizeof (buffer_Ps) - 1)))
		printf("test 'Ps' failed\n");
}