/**
 * fichier: logic.l
 * auteur: Johann Rosain
 * date: 29/03/2022
 **/
%{
#define YYSTYPE int

#include <stdlib.h>
#include <stdio.h>

#include "y.tab.h"
%}
%option noyywrap
%%
[ \t]+      { /* Filtrage des blancs */ }
[a-z]       { yylval = yytext[0]; return (VAR); }
0|1         { yylval = yytext[0] - '0'; return (IDENT); }
\|          { return (OR); }
->          { return (IMP); }
==          { return (EQUAL); }
\^          { return (XOR); }
&           { return (AND); }
!           { return (NOT); }
\(          { return (OPEN); }
\)          { return (CLOSE); }
quit        { return (QUIT); }
.|\n        { return yytext[0]; }
%%