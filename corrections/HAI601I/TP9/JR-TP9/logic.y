
 fichier: logic.y
 auteur: Johann Rosain
 date: 29/03/2022
%{
#define YYSTYPE int
int variables[26];

int yylex(); void yyerror(char *s);    
%}

%token IDENT VAR OR IMP EQUAL XOR AND NOT OPEN CLOSE QUIT

%left EQUAL
%left NOT 
%left OR XOR
%left AND 
%right IMP
%left '='

%%
liste:                  {}
 |     liste ligne      {}
 ;

ligne: '\n'             {}
 |     error '\n'       { yyerrok; }
 |     QUIT '\n'        { return 0; }
 |     expr '\n'        { printf("Résultat: %d\n", $1); }
 ;

expr: OPEN expr CLOSE   { $$ = $2; }
 |    expr EQUAL expr   { $$ = ($1 == $3); }
 |    NOT expr          { $$ = !($2); }
 |    expr OR expr      { $$ = ($1 || $3); }
 |    expr XOR expr     { $$ = ($1 ^ $3); }
 |    expr AND expr     { $$ = ($1 && $3); }
 |    expr IMP expr     { $$ = (!($1) || $3); }
 |    IDENT             { $$ = $1; }
 |    VAR '=' expr      { variables[$1 - 'a'] = $3; $$ = $3; }
 |    VAR               { $$ = variables[$1 - 'a']; }
%%

void yyerror(char *s) {
    fprintf(stderr, "%s\n", s);
}

int main() {
    yydebug = 0; 
    if (!yyparse()) {
        printf("Merci d'avoir utilisé la calculatrice logique CLI. Au revoir!\n");
    }
    return 0;
}