%{
    #include <stdio.h>

    int yylex(void);
    void yyerror(char*);
%}

%token OR IMPL EQUIV XOR AND NOT ZERO ONE
%type expr

%%
liste   :               {}
|           liste ligne {}
;
ligne   :         '\n'  { /* ligne vide */ }
|           error '\n'  { yyerrok; }
|           expr  '\n'  { printf("Valeur de l'expression : %i\n", $1);
                          printf("Donnez une autre expression booléenne : "); }
;
expr    :   expr OR expr    { $$ = $1 | $3; }
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
    printf("Ecrivez une expression booléenne : ");
    if (!yyparse()) {
        printf("\nExpression reconnue\n");
    }
    else {
        printf("\nExpression non reconnue\n");
    }

    return 0;
}