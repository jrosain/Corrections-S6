%{
#include <stdio.h>

enum Token {
    WORD = 300,
    LIST,
    TAB,
    NEWLINE,
    BREAKLINE,
    ITALIC,
    BOLD,
};
// Compteur du nombre de # pour un titre
int yytitle = 0;
%}
%%
(\t|" "{2})             { return TAB; /* On accepte une tabulation comme ayant 2 espaces ou + */ }
\*[a-zA-Z0-9_]+\*       { return ITALIC; }
\*\*[a-zA-Z0-9_]+\*\*   { return BOLD; }
[*\-]                   { return LIST; }
(#" ")                  { ++yytitle; /* On veut enlever l'espace avant le titre */ }
#                       { ++yytitle; /* On compte le nombre de # */ }
^[\t ]*\n               { /* filtrage des lignes vides */ }
\n\n                    { return BREAKLINE; /* Saut de ligne */ }
\n                      { return NEWLINE; }
.                       { return WORD; }
%%
int main(int argc, char **argv) {
    if (argc != 3) {
        printf("Utilisation : %s fichier.md fichier.html\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    yyin = fopen(argv[1], "r");
    yyout = fopen(argv[2], "w");

    if (yyin == NULL || yyout == NULL) {
        perror("Erreur lors de l'ouverture d'un fichier ");
        exit(EXIT_FAILURE);
    }

    // Variables pour les listes. Pile à 1000 éléments max. 
    int stack[1000];
    stack[0] = 0;
    int stacklen = 0, currentIndent = 0;
    // Si on a ouvert un tag, on veut le fermer. Cette variable garde la dernière balise ouverte à fermer.
    char closeTag[100];
    closeTag[0] = '\0';
    int c;
    while ((c = yylex()) != 0) {
        switch (c) {
        case LIST:
            // Première liste OU liste imbriquée : ajouter un <ul>
            if ((currentIndent == 0 && stack[stacklen] == 0) || currentIndent > stack[stacklen]) {
                fprintf(yyout, "<ul>");
                stack[++stacklen] = currentIndent;
            }
            int indent = stack[stacklen];
            // Soit c'est un item, soit c'est un item ET c'est la fin de la liste.
            if (currentIndent == stack[0] && stack[stacklen] != 0) {
                sprintf(closeTag, "</li></ul>");
            }
            else {
                sprintf(closeTag, "</li>");
            }
            // On print </ul> tant qu'on peut fermer des listes ouvertes
            while (indent > currentIndent) {
                fprintf(yyout, "</ul>");
                indent = stack[--stacklen];
            }
            fprintf(yyout, "<li>");
            break;
        case WORD:
            // Balise titre égale au nombre de #
            if (yytitle) {
                fprintf(yyout, "<h%i>", yytitle);
                sprintf(closeTag, "</h%i>", yytitle);
                yytitle = 0;
            }
            ECHO;
            break;
        case TAB:
            ++currentIndent;
            break;
        case NEWLINE :
            fprintf(yyout, "%s", closeTag);
            closeTag[0] = '\0';
            currentIndent = 0;
            ECHO;
            break; 
        case BREAKLINE :
            fprintf(yyout, "%s", closeTag);
            closeTag[0] = '\0';
            currentIndent = 0;
            fprintf(yyout, "<br />\n");
            break;
        case ITALIC :
            // Transformation du * en \0
            yytext[yyleng - 1] = '\0';
            // Attention, prendre après le premier * !
            fprintf(yyout, "<i>%s</i>", yytext + 1);
            break;
        case BOLD :
            // Transformation du premier * en \0
            yytext[yyleng - 2] = '\0';
            // Attention : prendre après le 2ème *
            fprintf(yyout, "<b>%s</b>", yytext + 2);
            break;
        }
    }
}