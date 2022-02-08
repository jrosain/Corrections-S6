%{
#define ONESPACE 300
#define OK       301
%}
%%
^[\t ]*\n           { /* filtrer, ligne vide */ }
^[\t ]+             { /* filtrer, début de ligne */ }
[\t ]+$             { /* filtrer, fin de ligne (le $ remplace le \n) */ }
[\t ]+              { return ONESPACE; }  
.|\n                { return OK; }
%%
#include <stdio.h>

int main(int argc, char **argv) {
    if (argc != 3) {
        printf("Utilisation : %s file_in file_out", argv[0]);
        exit(EXIT_FAILURE);
    }

    yyin = fopen(argv[1], "r");
    yyout = fopen(argv[2], "w");
    if (yyin == NULL || yyout == NULL) {
        perror("Erreur lors de l'ouverture du fichier ");
        exit(EXIT_FAILURE);
    }                                           

    int j;
    while ((j = yylex()) != 0) {
        switch(j) {
        case ONESPACE :
            fprintf(yyout, " ");
            break;
        case OK :
            fprintf(yyout, "%s", yytext);
            break;
        default :
            printf("Lexeme filtré : %s\n", yytext);
            break;
        }
    }

    fclose(yyin); fclose(yyout);
    return 0;
}