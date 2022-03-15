/** 
 * @file analdesc.c        
 * @author Michel Meynard
 * @brief Analyse descendante récursive d'expression arithmétique
 *
 * Ce fichier contient un reconnaisseur d'expressions arithmétiques composée de 
 * littéraux entiers sur un car, des opérateurs +, * et du parenthésage ().
 * Remarque : soit rediriger en entrée un fichier, soit terminer par deux 
 * caractères EOF (Ctrl-D), un pour lancer la lecture, l'autre comme "vrai" EOF.
 */
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#include "arbin.h"

#define AVANCER { jeton = getchar(); numcar++; }
#define TEST_AVANCE(prevu) { if (jeton == (prevu)) AVANCER else ERREUR_SYNTAXE }
#define ERREUR_SYNTAXE { printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1); } 

Arbin E(); Arbin R(Arbin gauche); Arbin T(); Arbin S(Arbin gauche); Arbin F(); 

int jeton;                                  /* caractère courant du flot d'entrée */
int numcar = 0;                             /* numero du caractère courant (jeton) */

Arbin E() {                                 /* regle : E->TR */
    return R(T());
}

Arbin R(Arbin gauche) {                     /* regle : R->+TR|epsilon */
    if (jeton == '+') {                     
        AVANCER
        return R(ab_construire('+', gauche, T()));
    }
    return gauche;
}

Arbin T() {                                  /* regle : T->FS */
    return S(F());
}

Arbin S(Arbin gauche) {                      /* regle : S->*FS|epsilon */
    if (jeton == '*') {                     
        AVANCER
        return S(ab_construire('*', gauche, F()));
    }
    return gauche;
}

Arbin F() {                                  /* regle : F->(E)|0|1|...|9 */
    if (jeton == '(') {                     
        AVANCER
        Arbin e = E();
        TEST_AVANCE(')')
        return e;
    }
    else {
        if (isdigit(jeton)) {
            int val = jeton;
            AVANCER
            return ab_construire(val, ab_creer(), ab_creer());
        }
        else {
            ERREUR_SYNTAXE
        }
    }
}

int main() {                             
    AVANCER			                        /* initialiser jeton sur le premier car */
    Arbin abr = E();                        /* axiome */
    if (jeton == '\n') {                    /* expression reconnue et rien après */
        printf("\nMot reconnu.\n"); 
        ab_afficher(abr); 
    }
    else {
        ERREUR_SYNTAXE                      /* expression reconnue mais il reste des car */
    }
    ab_vider(&abr);
    return 0;
}