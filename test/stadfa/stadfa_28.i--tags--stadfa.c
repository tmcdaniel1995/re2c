/* Generated by re2c */

{
	YYCTYPE yych;
	unsigned int yyaccept = 0;
	if ((YYLIMIT - YYCURSOR) < 5) YYFILL(5);
	yych = *(YYMARKER = YYCURSOR);
	switch (yych) {
	case 'a':	goto yy3;
	case 'b':	goto yy5;
	case 'c':	goto yy7;
	default:	goto yy2;
	}
yy2:
	{}
yy3:
	yych = *++YYCURSOR;
	yyt4 = yyt1;
	switch (yych) {
	case 'a':
	case 'c':	goto yy9;
	default:	goto yy4;
	}
yy4:
	YYCURSOR = YYMARKER;
	switch (yyaccept) {
	case 0: 	goto yy2;
	case 1: 	goto yy8;
	default:
		yyt2 = yyt1;
		yyt1 = yyt3;
		YYMTAGN (yyt1);
		goto yy6;
	}
yy5:
	yych = *++YYCURSOR;
	yyt3 = yyt2;
	switch (yych) {
	case 'b':	goto yy10;
	case 'c':	goto yy12;
	default:
		yyt2 = yyt1;
		YYMTAGN (yyt2);
		yyt1 = yyt3;
		YYMTAGP (yyt1);
		goto yy6;
	}
yy6:
	x = yyt1;
	y = yyt2;
	{}
yy7:
	yyaccept = 1;
	yych = *(YYMARKER = ++YYCURSOR);
	yyt4 = yyt1;
	yyt3 = yyt2;
	YYMTAGPD (yyt1);
	switch (yych) {
	case 'a':	goto yy9;
	case 'c':	goto yy13;
	default:	goto yy8;
	}
yy8:
	{}
yy9:
	yych = *++YYCURSOR;
	switch (yych) {
	case 'a':
	case 'c':	goto yy14;
	default:	goto yy4;
	}
yy10:
	++YYCURSOR;
	if (YYLIMIT <= YYCURSOR) YYFILL(1);
	yych = *YYCURSOR;
	yyt3 = yyt2;
	YYMTAGPD (yyt3);
	YYMTAGPD (yyt2);
	switch (yych) {
	case 'b':	goto yy10;
	case 'c':	goto yy12;
	default:
		yyt2 = yyt1;
		YYMTAGN (yyt2);
		yyt1 = yyt3;
		YYMTAGP (yyt1);
		goto yy6;
	}
yy12:
	++YYCURSOR;
	if (YYLIMIT <= YYCURSOR) YYFILL(1);
	yych = *YYCURSOR;
	yyt2 = yyt3;
	switch (yych) {
	case 'b':	goto yy15;
	default:
		yyt2 = yyt1;
		YYMTAGN (yyt2);
		yyt1 = yyt3;
		YYMTAGN (yyt1);
		goto yy6;
	}
yy13:
	yyaccept = 2;
	yych = *(YYMARKER = ++YYCURSOR);
	switch (yych) {
	case 'a':
	case 'c':	goto yy14;
	default:
		yyt2 = yyt1;
		yyt1 = yyt3;
		YYMTAGN (yyt1);
		goto yy6;
	}
yy14:
	yych = *++YYCURSOR;
	switch (yych) {
	case 'a':
	case 'c':	goto yy16;
	default:	goto yy4;
	}
yy15:
	++YYCURSOR;
	if (YYLIMIT <= YYCURSOR) YYFILL(1);
	yych = *YYCURSOR;
	yyt3 = yyt2;
	YYMTAGN (yyt3);
	YYMTAGN (yyt2);
	switch (yych) {
	case 'b':	goto yy10;
	case 'c':	goto yy12;
	default:
		yyt2 = yyt1;
		YYMTAGN (yyt2);
		yyt1 = yyt3;
		YYMTAGP (yyt1);
		goto yy6;
	}
yy16:
	yych = *++YYCURSOR;
	switch (yych) {
	case 'a':
	case 'c':	goto yy17;
	default:	goto yy4;
	}
yy17:
	++YYCURSOR;
	yyt1 = yyt4;
	yyt3 = yyt2;
	yyt2 = yyt1;
	YYMTAGN (yyt2);
	yyt1 = yyt3;
	YYMTAGN (yyt1);
	goto yy6;
}

stadfa/stadfa_28.i--tags--stadfa.re:4:3: warning: rule matches empty string [-Wmatch-empty-string]
