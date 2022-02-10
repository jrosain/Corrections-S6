/**
 * @file analex.c  
 * @author Michel Meynard
 * @brief Prog principal définissant et appelant analex().
 */
#define UNSEEN -1

#include <stdio.h>
#include <string.h>

#include "afd.h"		// Définition de l'AFD et des JETONS
#include "analex.h"		// Définition de la fonction analex()

/* Lexème courant de taille maxi 1024 */
char lexeme[1024];
/* Débogage */		
int DEBUG = 0;			

int main() {
    // AFD de l'utilisateur qui représente a(b+c)|bd
    creerAfd();

    // Jeton
    int j;
    // S'arrête quand j == 0.
    while((j = analex())) {
        printf("\nRésultat : Jeton = %d ; Lexeme = %s\n", j, lexeme);
    }

    return 0;
}

/** 
 * lit dans l'entrée standard le mot le plus long se terminant en un état final 
 * de l'automate défini par TRANS, puis retourne le JETON correspondant.
 * @returns le JETON entier correspondant à l'état final de l'AFD
 */
int analex(){
    int etat = EINIT;
    int efinal = UNSEEN;
    int lfinal = 0;

    int c;

    lexeme[0] = '\0';

    while ((c = getchar()) != EOF && TRANS[etat][c] != INVALID_TRANS) {
        strncat(lexeme, (char*)&c, 1);

        if (DEBUG) 
            printf("%i -- %c --> %i ;", etat, c, TRANS[etat][c]);

        etat = TRANS[etat][c];
        if (JETON[etat]) {
            efinal = etat;
            lfinal = strlen(lexeme);
        }    
    } 

    // Le dernier caractère est un état final.
    if (JETON[etat]) {
        ungetc(c, stdin);
        // Si JETON[etat] < 0, alors c'est un caractère à ne pas traiter (vide / commentaires).
        return (JETON[etat] < 0 ? analex() : JETON[etat]);
    }
    // Un état final a été repéré dans le lexeme
    else if (efinal > UNSEEN){		
        ungetc(c, stdin);
        for(int i = strlen(lexeme) - 1; i >= lfinal; i--)
            ungetc(lexeme[i], stdin);
        lexeme[lfinal] = '\0';
        return (JETON[efinal] < 0 ? analex() : JETON[efinal]);
    }
    // Il n'y a rien du tout
    else if (strlen(lexeme) == 0 && c == EOF)
        return 0;
    // Si le premier caractère ne match rien, on renvoie seulement lui.
    else if (strlen(lexeme) == 0){
        lexeme[0] = c;
        lexeme[1] = '\0';
        return c;
    }
    // Non reconnu, on renvoie le premier caractère du lexeme.
    else {
        ungetc(c, stdin);		
        for(int i = strlen(lexeme) - 1; i >= 1; i--)
            ungetc(lexeme[i], stdin);
        lexeme[1] = '\0';
        return lexeme[0];
    }
}