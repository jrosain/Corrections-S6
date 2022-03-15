#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#include "arbin.h"

/* les macros sont des blocs : pas de ';' apres */
#define AVANCER {jeton=getchar();numcar++;}
#define TEST_AVANCE(prevu) {if (jeton==(prevu)) AVANCER else ERREUR_SYNTAXE}
#define ERREUR_SYNTAXE {printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1);} 

Arbin E(void); Arbin R(Arbin); Arbin T(void); Arbin S(Arbin); Arbin F(void); /* déclars */

int jeton;                      /* caractère courant du flot d'entrée */
int numcar = 0;                 /* numero du caractère courant (jeton) */

Arbin E(void) {
  return R(T());                /* regle : E->TR */
}

Arbin R(Arbin g) {
    if (jeton == '+') {         /* regle : R->+TR */
        AVANCER
        return R(ab_construire('+', g, T()));
    }
    else return g;              /* regle : R->epsilon */
}

Arbin T(void) {
    return S(F());              /* regle : T->FS */
}

Arbin S(Arbin g) {
    if (jeton == '*') {         /* regle : S->*FS */
        AVANCER
        return S(ab_construire('*', g, F()));
    }
    else return g;               /* regle : S->epsilon */
}

Arbin F(void) {
    if (jeton == '(') {         /* regle : F->(E) */
        AVANCER
        Arbin a = E();
        TEST_AVANCE(')')
        return a;
    }
    else if (isdigit(jeton)) {  /* regle : F->0|1|...|9 */
        Arbin a = ab_construire(jeton, NULL, NULL);
        AVANCER
        return a;
    }
    else ERREUR_SYNTAXE
}

int main(void) {                /* Fonction principale */
    AVANCER			            /* initialiser jeton sur le premier car */
    Arbin a = E();              /* axiome */
    if (jeton == EOF) {         /* expression reconnue et rien après */
        printf("\nMot reconnu\n");
        ab_afficher(a);
    }
    else ERREUR_SYNTAXE         /* expression reconnue mais il reste des car */
    return 0;
}
