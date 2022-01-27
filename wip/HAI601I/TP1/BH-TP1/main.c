/**
 * @file main.c 
 * @author Michel Meynard
 * @brief Prog principal appelant analex()
**/

#include <stdio.h>
#include <string.h>

#include "afd.h"
#include "analex.h"

int main() {
    // Création de notre automate pour l'utiliser
    creerAfd();

    // Affichage dans la console
    char* invite = "Saisissez un(des) mot(s) matchant l'automate du TP suivi de EOF (CTRL-D) SVP : ";
    printf("%s", invite);

    int j;
    while((j = analex())) {
        printf("\nRésultat : Jeton = %d ; Lexeme = %s", j, lexeme);
    }

    return 0;
}
