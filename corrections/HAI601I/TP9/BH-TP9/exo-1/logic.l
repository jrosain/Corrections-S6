%{
#include "y.tab.h"
%}

%option noyywrap

%%
[ \t]   { /* Filtrage blancs */ }
0       { yylval = 0; return ZERO; }
1       { yylval = 1; return ONE; }
&       { return AND; }
\|      { return OR; }
\^      { return XOR; }
!       { return NOT; }
->      { return IMPL; }
==      { return EQUIV; }
.|\n    { return yytext[0]; }
%%