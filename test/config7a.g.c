/* Generated by re2c */
#line 1 "config7a.g.re"
{

#line 6 "<stdout>"
	{
		YYCTYPE yych;

		if(YYLIMIT == YYCURSOR) YYFILL(1);
		yych = *YYCURSOR;
		if(yych <= 'E') {
			if(yych <= '@') goto yy4;
			if(yych >= 'E') goto yy4;
		} else {
			if(yych <= 'G') goto yy2;
			if(yych <= '`') goto yy4;
			if(yych >= 'h') goto yy4;
		}
yy2:
		++YYCURSOR;
#line 10 "config7a.g.re"
		{ return 1; }
#line 24 "<stdout>"
yy4:
		++YYCURSOR;
#line 12 "config7a.g.re"
		{ return -1; }
#line 29 "<stdout>"
	}
}
#line 14 "config7a.g.re"

