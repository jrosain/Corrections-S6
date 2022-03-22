%{
#include <stdio.h>
#include "arbin.h"
int yylex(); void yyerror(char *s);    
%}
%union {
    int c;
    Arbin a;
};
%token<c> SYMBOLE
%type<a> S E T F

%left '*' '|'
%%
liste:              { /* epsilon, fin */ }
 |     liste ligne  {}
 ;

ligne: '\n'         { /* Filtrage */ } 
 |     S '\n'       { ab_afficher($1); }
 ;

S: S '|' E          { $$ = ab_construire('|', $1, $3); }
 | E                { $$ = $1; }
 ;

E: E T              { $$ = ab_construire('.', $1, $2); }
 | T                { $$ = $1; }
 ;

T: T '*'            { $$ = ab_construire('*', $1, ab_creer()); }
 | F                { $$ = $1; }
 ;

F: '(' S ')'        { $$ = $2; }
 | SYMBOLE          { $$ = ab_construire($1, ab_creer(), ab_creer()); }
 ;
%%

int yylex() {
    int c = getchar();
    if ((c >= 'a' && c <= 'z') || c == '@' || c == '0') {
        yylval.c = c;
        return SYMBOLE;
    }
    return c;
}

void yyerror(char *s) {
    fprintf(stderr, "%s\n", s);
}

int main() {
    yydebug = 0; 
    return yyparse();
}