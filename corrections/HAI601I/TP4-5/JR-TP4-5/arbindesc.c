/**
 * fichier: arbindesc.c
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

#include "arbin.h"

#define AVANCER { jeton = getchar(); numcar++; }
#define TEST_AVANCE(prevu) { if (jeton == (prevu)) AVANCER else ERREUR_SYNTAXE }
#define ERREUR_SYNTAXE { printf("\nMot non reconnu : erreur de syntaxe \
au caractère numéro %d \n",numcar); exit(1); } 

Arbin E(); Arbin R(); Arbin T(); Arbin S(); Arbin F(); 

int jeton;                                  /* caractère courant du flot d'entrée */
int numcar = 0;                             /* numero du caractère courant (jeton) */

Arbin E() {                                 /* regle : E->TR */
    Arbin t = T();
    Arbin r = R();
    // R() a généré epsilon, on ne prend que le sous-arbre T().
    if (ab_vide(r)) {
        return t;
    }
    // R() est une opération :
    //  1 - On prend sa racine et son sag et on fait un sous-arbre contenant l'opération 
    //  2 - Le sous-arbre droit devient le parent :
    //      * Transfert de la racine du sad en tant que racine de l'arbre
    //      * On récupère le fils non nul du sad pour le placer en sad.
    Arbin op = ab_construire(ab_racine(r), t, ab_sag(r));
    if (ab_vide(ab_sad(r))) {
        return op;
    }
    return ab_construire(ab_racine(ab_sad(r)), op, ab_sag(ab_sad(r))); 
}

Arbin R() {                                  /* regle : R->+TR|epsilon */
    Arbin rac = ab_creer();
    if (jeton == '+') {                     
        AVANCER
        Arbin t = T();
        Arbin r = R();
        rac = ab_construire('+', t, r);
    }
    return rac;
}

Arbin T() {                                  /* regle : T->FS */
    Arbin f = F();
    Arbin s = S();
    if (ab_vide(s)) {
        return f;
    }
    Arbin op = ab_construire(ab_racine(s), f, ab_sag(s));
    if (ab_vide(ab_sad(s))) {
        return op;
    }
    return ab_construire(ab_racine(ab_sad(s)), op, ab_sag(ab_sad(s))); 
}

Arbin S() {                                  /* regle : S->*FS|epsilon */
    Arbin rac = ab_creer();
    if (jeton == '*') {                     
        AVANCER
        Arbin f = F();
        Arbin s = S();
        rac = ab_construire('*', f, s);
    }
    return rac;
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