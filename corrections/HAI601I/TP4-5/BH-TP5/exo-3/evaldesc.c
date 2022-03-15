#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

/* les macros sont des blocs : pas de ';' apres */
#define AVANCER {jeton=getchar();numcar++;}
#define TEST_AVANCE(prevu) {if (jeton==(prevu)) AVANCER else ERREUR_SYNTAXE}
#define ERREUR_SYNTAXE {printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1);} 

int E(void); int R(int); int T(void); int S(int); int F(void); /* déclars */

int jeton;                      /* caractère courant du flot d'entrée */
int numcar = 0;                 /* numero du caractère courant (jeton) */

int E(void) {
  return R(T());                /* regle : E->TR */
}

int R(int g) {
    if (jeton == '+') {         /* regle : R->+TR */
        AVANCER
        return R(g + T());
    }
    return g;                   /* regle : R->epsilon */
}

int T(void){
    return S(F());              /* regle : T->FS */
}

int S(int g){
    if (jeton == '*') {         /* regle : S->*FS */
        AVANCER
        return S(g * F());
    }
    return g;                   /* regle : S->epsilon */
}

int F(void){
    if (jeton == '(') {         /* regle : F->(E) */
        AVANCER
        int val = E();
        TEST_AVANCE(')')
        return val;
    }
    else if (isdigit(jeton)) {  /* regle : F->0|1|...|9 */
        int val = jeton - '0';
        AVANCER
        return val;
    }
    else ERREUR_SYNTAXE
}

int main(void){                 /* Fonction principale */
    AVANCER			            /* initialiser jeton sur le premier car */
    int val = E();              /* axiome */
    if (jeton == EOF) {         /* expression reconnue et rien après */
        printf("\nMot reconnu\n"); 
        printf("Valeur = %i\n", val);
    }
    else ERREUR_SYNTAXE         /* expression reconnue mais il reste des car */
    return 0;
}
