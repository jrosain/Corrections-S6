/* Zone de définition */

%{
    enum TypeJeton {
        WORD = 1,
        NEW_LINE,
        SPACE,
    };
%}

/* Zone des règles */

%%
[^\ \n\t]+      { return WORD; } // Un mot
\n              { return NEW_LINE; } // Nouvelle ligne
.               { return SPACE; } // Les blancs restant
%%

/* Zone des fonctions C */

int main(int argc, char** argv) {
    if (argc != 2) {
        printf("Utilisation : %s in \n", argv[0]);
        exit(1);
    }
    
    yyin = fopen(argv[1], "r");

    int j;
    int nb_char = 0;
    int nb_line = 0;
    int nb_word = 0;

    while ((j=yylex()) != 0) {
        nb_char += yyleng;
        switch(j) {
            case WORD:
                nb_word += 1;
                break;
            case NEW_LINE:
                nb_line += 1;
                break;
            default:
                break;
        }
    }

    printf("Char : %i\n", nb_char);
    printf("Word : %i\n", nb_word);
    printf("Line : %i\n", nb_line);
    
    return 0;
}