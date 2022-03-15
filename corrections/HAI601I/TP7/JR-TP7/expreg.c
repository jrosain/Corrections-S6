/**
 * fichier: expreg.c
 * auteur: Johann Rosain
 * date: 15/03/2022
 **/
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#include "afd.h"

#define AVANCER { jeton = getchar(); numcar++; }
#define TEST_AVANCE(prevu) { if (jeton == (prevu)) AVANCER else ERREUR_SYNTAXE }
#define ERREUR_SYNTAXE { printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1); } 

Arbin union_(); Arbin runion(Arbin gauche); Arbin concat(); Arbin rconcat(Arbin gauche); Arbin etoile(); Arbin retoile(Arbin gauche); Arbin base();

int jeton;
int numcar = 0;

Arbin union_() {                        /* Règle: union -> concat runion */
    return runion(concat());
}

Arbin runion(Arbin gauche) {            /* Règle: runion -> |concat runion|@ */
    if (jeton == '|') {
        AVANCER
        Arbin droite = concat();
        if (ab_racine(droite) == '0')                                                   /* Optimisation: e|0 = e */
            return gauche;
        if (ab_racine(gauche) == '0')                                                   /* Optimisation: 0|e = e */
            return droite;
        return runion(ab_construire('|', gauche, droite));
    }
    return gauche;
}

Arbin concat() {                        /* Règle: concat -> etoile rconcat */
    return rconcat(etoile());
}

Arbin rconcat(Arbin gauche) {           /* Règle: rconcat -> etoile rconcat|@ */
    if ((jeton < 'a' || jeton > 'z') && jeton != '@' && jeton != '0') return gauche;
    if (ab_racine(gauche) == '0') {                                                     /* Optimisation: 0e = 0 */
        AVANCER
        return ab_construire('0', ab_creer(), ab_creer());
    }
    Arbin droite = etoile();
    if (ab_racine(gauche) == '@')                                                       /* Optimisation: @e = e */
        return droite;
    if (ab_racine(droite) == '@')                                                       /* Optimisation: e@ = e */
        return gauche;
    if (ab_racine(droite) == '0')                                                       /* Optimisation: e0 = 0 */
        return ab_construire('0', ab_creer(), ab_creer());
    return rconcat(ab_construire('.', gauche, droite));
}

Arbin etoile() {                        /* Règle: etoile -> base retoile */
    return retoile(base());
}

Arbin retoile(Arbin gauche) {           /* Règle: retoile -> *retoile|@ */
    if (jeton == '*') {
        AVANCER 
        if (ab_racine(gauche) == '@' || ab_racine(gauche) == '0')                       /* Optimisation: @* = 0* = @ */
            return retoile(ab_construire('@', ab_creer(), ab_creer()));
        if (ab_racine(gauche) != '*')                                                   /* Optimisation: e** = e* */
            return retoile(ab_construire('*', gauche, ab_creer()));
        if (ab_racine(gauche) == '*') 
            return retoile(gauche);
        
    }
    return gauche;
}

Arbin base() {                          /* Règle: base -> a|b|...|z|(union)|@|0 */
    if (jeton == '(') {
        AVANCER 
        Arbin u = union_();
        TEST_AVANCE(')')
        return u;
    }
    else {
        if ((jeton >= 'a' && jeton <= 'z') || jeton == '@' || jeton == '0') {
            int val = jeton;
            AVANCER
            return ab_construire(val, ab_creer(), ab_creer());
        }
        ERREUR_SYNTAXE
    }
}

int main() {
    printf("Veuillez saisir une expression régulière suivie de <Entrée> S.V.P.\n");
    AVANCER 
    Arbin expr = union_();
    if (jeton == '\n') {
        ab_afficher(expr);

        int n = nombreEtats(expr);
        printf("\nConstruction de l'AFD a %i états...\n", n);

        int **AFD = construireAFD(expr);
        afficherAFD(AFD, n);
        libererAFD(AFD, n);
    }
    else {
        printf("Erreur syntaxe %c\n", jeton);
        ERREUR_SYNTAXE
    }
    ab_vider(&expr);
    return 0;
}