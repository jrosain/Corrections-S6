#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

/* les macros sont des blocs : pas de ';' apres */
#define AVANCER {jeton=getchar();numcar++;}
#define TEST_AVANCE(prevu) {if (jeton==(prevu)) AVANCER else ERREUR_SYNTAXE}
#define ERREUR_SYNTAXE {printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1);} 

void E(void); void R(void); void T(void); void S(void); void F(void); /* déclars */

int jeton;                      /* caractère courant du flot d'entrée */
int numcar = 0;                 /* numero du caractère courant (jeton) */

void E(void) {
  T();                          /* regle : E->TR */
  R();
}

void R(void) {
    if (jeton == '+') {         /* regle : R->+TR */
        AVANCER
        T();
        printf("+");
        R();
    }
    else ;                      /* regle : R->epsilon */
}

void T(void){
    F();
    S();                        /* regle : T->FS */
}

void S(void){
    if (jeton == '*') {         /* regle : S->*FS */
        AVANCER
        F();
        printf("*");
        S();
    }
    else ;                      /* regle : S->epsilon */
}

void F(void){
    if (jeton == '(') {         /* regle : F->(E) */
        AVANCER
        E();
        TEST_AVANCE(')')
    }
    else if (isdigit(jeton)) {  /* regle : F->0|1|...|9 */
        printf("%c", jeton);
        AVANCER
    }
    else ERREUR_SYNTAXE
}

int main(void){                 /* Fonction principale */
    AVANCER			            /* initialiser jeton sur le premier car */
    E();                        /* axiome */
    if (jeton == EOF)           /* expression reconnue et rien après */
        printf("\nMot reconnu\n"); 
    else ERREUR_SYNTAXE         /* expression reconnue mais il reste des car */
    return 0;
}
