/**
 * fichier: postdesc.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
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
                             /* les macros sont des blocs : pas de ';' apres */
#define AVANCER { jeton = getchar(); numcar++; }
#define TEST_AVANCE(prevu) { if (jeton == (prevu)) AVANCER else ERREUR_SYNTAXE }
#define ERREUR_SYNTAXE { printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1); } 

void E(); void R(); void T(); void S(); void F(); 

int jeton;                                  /* caractère courant du flot d'entrée */
int numcar = 0;                             /* numero du caractère courant (jeton) */

void E() {                                  /* regle : E->TR */
    T();
    R();
}

void R() {                                  /* regle : R->+TR|epsilon */
    if (jeton == '+') {                     
        AVANCER
        T();
        printf("+");
        R();
    }
}

void T() {                                  /* regle : T->FS */
    F();
    S();
}

void S() {                                  /* regle : S->*FS|epsilon */
    if (jeton == '*') {                     
        AVANCER
        F();
        printf("*");
        S();
    }
}

void F() {                                  /* regle : F->(E)|0|1|...|9 */
    if (jeton == '(') {                     
        AVANCER
        E();
        TEST_AVANCE(')')
    }
    else {
        if (isdigit(jeton)) {
            printf("%c", jeton);
            AVANCER
        }
        else {
            ERREUR_SYNTAXE
        }
    }
}

int main() {                             
    AVANCER			                        /* initialiser jeton sur le premier car */
    E();                                    /* axiome */
    if (jeton == '\n') {                    /* expression reconnue et rien après */
        printf("\nMot reconnu.\n"); 
    }
    else {
        ERREUR_SYNTAXE                      /* expression reconnue mais il reste des car */
    }
    return 0;
}