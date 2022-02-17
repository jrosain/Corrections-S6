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

int E(); int R(int gauche); int T(); int S(int left); int F(); 

int jeton;                                  /* caractère courant du flot d'entrée */
int numcar = 0;                             /* numero du caractère courant (jeton) */

int E() {                                   /* regle : E->TR */    
    return R(T());
}

int R(int left) {                           /* regle : R->+TR|epsilon */
    if (jeton == '+') {                     
        AVANCER
        return R(left + T());
    }
    return left;
}

int T() {                                   /* regle : T->FS */
    return S(F());
}

int S(int left) {                           /* regle : S->*FS|epsilon */
    if (jeton == '*') {                     
        AVANCER
        return S(left * F());
    }
    return left;
}

int F() {                                   /* regle : F->(E)|0|1|...|9 */
    if (jeton == '(') {                     
        AVANCER
        int res = E();
        TEST_AVANCE(')')
        return res;
    }
    else {
        if (isdigit(jeton)) {
            int val = jeton - '0';
            AVANCER
            return val;
        }
        else {
            ERREUR_SYNTAXE
        }
    }
}

int main() {                             
    AVANCER			                        /* initialiser jeton sur le premier car */
    int result = E();                       /* axiome */
    if (jeton == '\n') {                    /* expression reconnue et rien après */
        printf("Mot reconnu. Résultat: %i\n", result); 
    }
    else {
        ERREUR_SYNTAXE                      /* expression reconnue mais il reste des car */
    }
    return 0;
}