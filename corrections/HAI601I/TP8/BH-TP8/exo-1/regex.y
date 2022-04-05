%{
    #include <stdio.h>
    #include "arbin.h"

    int yylex(void);
    void yyerror(char*);
%}

%union {
    int entier;
    Arbin arbre;
}

%type <arbre> S E T F
%token <entier> CHAR

%left '|'

%%
liste   :               {}
        |   liste ligne {};
ligne   :         '\n'  { /* ligne vide */ }
        |   error '\n'  { yyerrok;}
        |   S     '\n'  { printf("Affichage de l'arbre :\n");
                          ab_afficher($1);
                          printf("Donnez une autre expression régulière : "); };

S   :   S '|' E     { $$ = ab_construire('|', $1, $3); }
    |   E           { $$ = $1; };
E   :   E     T     { $$ = ab_construire('.', $1, $2); }
    |   T           { $$ = $1; };
T   :   T '*'       { $$ = ab_construire('*', $1, ab_creer()); }
    |   F           { $$ = $1; };
F   :   '(' S ')'   { $$ = $2; }
    |   CHAR        { $$ = ab_construire($1, ab_creer(), ab_creer()); };
%%

int yylex(void) {
    int c;
    
    while (((c = getchar()) == ' ') || (c == '\t'));

    if ((c >= 'a' && c <= 'z') || c == '@' || c == '0') {
        yylval.entier = c;
        return CHAR;
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