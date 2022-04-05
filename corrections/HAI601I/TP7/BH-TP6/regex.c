#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#include "afd.h"
#include "arbin.h"

/* les macros sont des blocs : pas de ';' apres */
#define AVANCER {jeton=getchar();numjeton++;}
#define TEST_AVANCE(prevu) {if (jeton==(prevu)) AVANCER else ERREUR_SYNTAXE}
#define ERREUR_SYNTAXE {printf("\nMot non reconnu : erreur de syntaxe \
au jeton numéro %d : %c\n",numjeton,jeton); exit(1);} 

Arbin S(void);
Arbin RT(Arbin);
Arbin T(void);
Arbin RE(Arbin);
Arbin E(void);
Arbin RS(Arbin);
Arbin F(void);

int jeton;                      /* caractère courant du flot d'entrée */
int numjeton = 0;               /* numero du caractère courant (jeton) */

int char_base(int jeton) {
    return jeton == '@' || jeton == '0' || (jeton >= 'a' && jeton <= 'z');
}

Arbin S(void) {
    return RS(E());             /* regle : S->ERS */
}

Arbin RS(Arbin g) {
    if (jeton == '|') {         /* regle : RS->|ERS */
        AVANCER
        Arbin d = E();
        if (g->val == '0') {    /* optimisation 0|e = e */
            return RS(d);
        }
        if (d->val == '0') {    /* optimisation e|0 = e */
            return RS(g);
        }
        return RS(ab_construire('|', g, d));
    }
    else return g;              /* regle : RS->epsilon */
}

Arbin E(void) {
    return RE(T());             /* regle : E->TRE */
}

Arbin RE(Arbin g) {
    if (jeton == '(' || char_base(jeton)) {         /* regle : RE->TRE */
        Arbin d = T();
        if (g->val == '@') {    /* optimisation @e = e */
            return RE(d);
        }
        if (d->val == '@') {    /* optimisation e@ = e */
            return RE(g);
        }
        if (g->val == '0') {    /* optimisation 0e = 0 */
            return RE(g);
        }
        if (d->val == '0') {    /* optimisation e0 = 0 */
            return RE(d);
        }
        return RE(ab_construire('.', g, d));
    }
    else return g;               /* regle : RE->epsilon */
}

Arbin T(void) {
    return RT(F());             /* regle : T->FRT */
}

Arbin RT(Arbin g) {
    if (jeton == '*') {         /* regle : RT->*RT */
        AVANCER
        if (g->val == '*') {    /* optimisation e**=e* */
            return RT(g);
        }
        if (g->val == '@') {    /* optimisation @*=@ */
            return RT(g);
        }
        if (g->val == '0') {    /* optimisation 0*=@ */
            return RT(ab_construire('@', NULL, NULL));
        }
        return RT(ab_construire('*', g, NULL));
    }
    else return g;              /* regle : RT->epsilon */
}

Arbin F(void) {
    if (jeton == '(') {         /* regle : F->(S) */
        AVANCER
        Arbin a = S();
        TEST_AVANCE(')')
        return a;
    }
    else if (char_base(jeton)) {  /* regle : F->a|...|z|0|@ */
        Arbin a = ab_construire(jeton, NULL, NULL);
        AVANCER
        return a;
    }
    else ERREUR_SYNTAXE
}

int main(void) {                /* Fonction principale */
    AVANCER			            /* initialiser jeton sur le premier car */
    Arbin a = S();              /* axiome */
    if (jeton == EOF) {         /* expression reconnue et rien après */
        printf("\nMot reconnu\n");
        ab_afficher(a);

        int nb_etats = nombre_etat(a);
        printf("\nNombre d'état de l'AFN : %i\n\n", nb_etats);

        int** afn = creer_afn(a, nb_etats);
        struct Etat etats = remplir_afn(a, afn);

        afficher_afn(afn, nb_etats, etats);

        suppr_afn(afn, nb_etats);
    }
    else ERREUR_SYNTAXE         /* expression reconnue mais il reste des car */

    ab_vider(&a);

    return 0;
}
