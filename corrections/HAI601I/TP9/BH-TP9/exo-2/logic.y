%{
    #include <stdio.h>

    int yylex(void);
    void yyerror(char*);

    int affect[26];

    int erreurSemantique = 0;

    #define NON_AFFECT 1
%}

%token OR IMPL EQUIV XOR AND NOT ZERO ONE, SYMBOL
%type expr

%%
liste   :               {}
|           liste ligne {}
;
ligne   :         '\n'  { /* ligne vide */ }
|           error '\n'  { yyerrok; }
|           expr  '\n'  { if (!erreurSemantique) {
                            printf("Valeur de l'expression : %i\n", $1);
                        } else {
                            printf("Erreur : variable utilisée mais non assignée.\n");
                            erreurSemantique = 0;
                        }
                        printf("Donnez une autre expression booléenne : "); }
;
expr    :   expr OR expr    { $$ = $1 | $3; }
|           SYMBOL '=' expr { $$ = $3; affect[$1 - 'a'] = $3; }
|           SYMBOL          { if (affect[$1 - 'a'] != -1) {
                                $$ = affect[$1 - 'a'];
                            } else {
                                erreurSemantique = NON_AFFECT;
                            }}
|           expr AND expr   { $$ = $1 & $3; }
|           expr XOR expr   { $$ = $2 ^ $3; }
|           NOT expr        { $$ = ! $2; }
|           expr EQUIV expr { $$ = $1 == $3; }
|           expr IMPL expr  { $$ = ! $1 || $3; }
|           '(' expr ')'    { $$ = $2; }
|           ONE             { $$ = $1; }
|           ZERO            { $$ = $1; }
;
%%

void yyerror(char* s) {
    fprintf(stderr, "%s\n", s);
}

int main() {
    // Initialisation
    for (int i = 0; i < 26; ++i) {
        affect[i] = -1;
    }

    printf("Ecrivez une expression booléenne : ");
    yyparse();

    return 0;
}