%{
    #include <stdio.h>
    #include "arbin.h"

    int yylex(void);
    void yyerror(char*);
%}

%union {
    int i;
    Arbin a;
}

%type <a> expr
%token <i> SYMBOLE

%left '|'
%left CONCAT
%left '*'

%nonassoc '(' SYMBOLE

%%
liste   :               {}
|           liste ligne {}
;
ligne   :         '\n'  { /* ligne vide */ }
|           error '\n'  { yyerrok;}
|           expr  '\n'  { printf("Affichage de l'arbre :\n");
                          ab_afficher($1);
                          printf("Donnez une autre expression régulière : "); }
;
    
expr :  '(' expr ')'            { $$ = $2; }
|       expr expr %prec CONCAT  { $$ = ab_construire('.', $1, $2); }
|       expr '|' expr           { $$ = ab_construire('|', $1, $3); }
|       expr '*'                { $$ = ab_construire('*', $1, ab_creer()); }
|       SYMBOLE                 { $$ = ab_construire(yylval.i, ab_creer(), ab_creer()); }
;
%%


int yylex(void) {
    int c;
    
    while (((c = getchar()) == ' ') || (c == '\t'));

    if ((c >= 'a' && c <= 'z') || c == '@' || c == '0') {
        yylval.i = c;
        return SYMBOLE;
    }

    return c;
}

void yyerror(char* s) {
    fprintf(stderr, "%s\n", s);
}

int main() {
    printf("Ecrivez une expression régulière : ");
    if (!yyparse()) {
        printf("\nExpression reconnue\n");
    }
    else {
        printf("\nExpression non reconnue\n");
    }

    return 0;
}