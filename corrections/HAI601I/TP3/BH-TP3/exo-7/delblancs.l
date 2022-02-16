/* Zone de définition */

%{
    enum TypeJeton {
        WHITE_LINE = 1,
        WHITE_BEGIN,
        WHITE_END,
        WHITE,
        CHAR,
    };
%}

/* Zone des règles */

%%
^[\t\n ]*\n  { return WHITE_LINE; } // Lignes blanches
^[\t ]+      { return WHITE_BEGIN; } // Début de lignes
[\t ]+\n     { return WHITE_END; } // Fin de lignes
[\t ]+       { return WHITE; } // Blanc à l'intérieur d'une ligne
(.|\n)       { return CHAR; }
%%

/* Zone des fonctions C */

int main(int argc, char** argv) {
    if (argc != 3) {
        printf("Utilisation : %s in out\n", argv[0]);
        exit(1);
    }
    
    yyin = fopen(argv[1], "r");
    yyout = fopen(argv[2], "w");

    int j;

    while ((j=yylex()) != 0) {
        switch(j) {
            case WHITE_LINE:
            case WHITE_BEGIN:
                break;
            case WHITE_END:
                fputc('\n', yyout);
                break;
            case WHITE:
                fputc(' ', yyout);
                break;
            case CHAR:
                ECHO;
                break;
        }
    }
    
    return 0;
}