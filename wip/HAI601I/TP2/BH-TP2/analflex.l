/* Zone de définition */

%{
    enum TypeJeton {
        KEY = 1,
        ID,
        LITENT,
        FLOTENT,
    };

    union {
        int i;
        char* s;
        double d;
    } yylval;
%}

/* Zone des règles */

%%
if|else|(th(en|row))    { return KEY; }
0x?[0-9]+               { yylval.i = atoi(yytext); return LITENT; }
[a-zA-Z][a-zA-Z0-9_]*   { yylval.s = (char*) malloc(strlen(yytext)+1); strcpy(yylval.s, yytext); return ID; }
([0-9]+\.[0-9]*|\.[0-9]+)([eEdD][+-]?[0-9]+)?f? { yylval.d = atof(yytext); return FLOTENT; }
([ \t\n]*)|(\/\/.*)|(\/\*([^\*]*\*+[^\*\/])*[^\*]*\*+\/) {}
.|\n                    { return yytext[0]; }
%%

/* Zone des fonctions C */

int main(int argc, char** argv) {
    if (argc > 1) {
        yyin = fopen(argv[1], "r");
    }

    int j;

    printf("Saisissez du texte suivi de EOF (CTRL-D) SVP : ");

    while ((j=yylex()) != 0) {
        switch(j) {
            case KEY:
                printf("\nJeton : %i; de lexeme %s", j, yytext);
                break;
            case ID:
                printf("\nJeton : %i; de lexeme %s", j, yylval.s);
                break;
            case LITENT:
                printf("\nJeton : %i; de lexeme %i", j, yylval.i);
                break;
            case FLOTENT:
                printf("\nJeton : %i; de lexeme %lf", j, yylval.d);
                break;
            default:
                printf("\nJeton : %i; de lexeme %s", j, yytext);
                break;
        }
    }

	printf("\n");
}