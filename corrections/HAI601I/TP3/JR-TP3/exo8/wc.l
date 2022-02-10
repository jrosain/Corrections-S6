%{
#include <stdio.h>

enum Token {
    WORD = 300,
    CHAR,
    LINE,
};
%}
%%
[^ \t\n]+   { return WORD; }
" "         { return CHAR; }
\n          { return LINE; }
%%
int main(int argc, char **argv) {
    if (argc != 3) {
        printf("Utilisation : %s [OPTION] fichier", argv[0]);
        exit(EXIT_FAILURE);
    }

    yyin = fopen(argv[2], "r");
    if (yyin == NULL) {
        perror("Erreur lors de la lecture du fichier ");
        exit(EXIT_FAILURE);
    }

    int nchars = 0, nwords = 0, nlines = 0;
    int c;
    while ((c = yylex()) != 0) {
        switch(c) {
        case CHAR :
            ++nchars;
            break;
        case WORD :
            nchars += yyleng;
            ++nwords; 
            break;
        case LINE :
            ++nchars;
            ++nlines;
            break;
        }
    }

    if (argv[1][1] == 'm') {
        // Pour une raison inconnue, j'ai un caractère de plus que ce qu'il y a vraiment
        printf("Nombre de caractères : %i\n", nchars);
    }
    else if (argv[1][1] == 'w') {
        printf("Nombre de mots : %i\n", nwords);
    }
    else if (argv[1][1] == 'l') {
        printf("Nombre de lignes : %i\n", nlines);
    }
}