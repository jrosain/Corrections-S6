#include "afd.h"
#include "arbin.h"
#include <stdlib.h>
#include <stdio.h>

struct Etat arbre_vers_afn(Arbin a, int** afn);
int i;

int nombre_etat(Arbin a) {
    if (a == NULL) {
        return 0;
    }
    if (a->val == '.') {
        return nombre_etat(a->fd) + nombre_etat(a->fg);
    }
    if (a->val == '|') {
        return nombre_etat(a->fd) + nombre_etat(a->fg) + 2;
    }
    if (a->val == '*') {
        return nombre_etat(a->fd) + nombre_etat(a->fg) + 2;
    }
    return 2;
}

int** creer_afn(Arbin a, int nb_etats) {
    int** afn = malloc(nb_etats * sizeof(int*));
    for (int i = 0; i < nb_etats; ++i) {
        afn[i] = malloc(3 * sizeof(int));
        afn[i][0] = afn[i][1] = afn[i][2] = -1;
    }
    return afn;
}

struct Etat remplir_afn(Arbin a, int** afn) {
    i = 0;
    return arbre_vers_afn(a, afn);
}

struct Etat arbre_vers_afn(Arbin a, int** afn) {
    struct Etat etat;

    if (a->fd == NULL && a->fg == NULL) {
        afn[i][0] = a->val;
        afn[i][1] = i + 1;
        
        etat.debut = i;
        etat.arrivee = i + 1;

        i += 2;
    }
    else if (a->val == '.') {
        struct Etat etat_fg = arbre_vers_afn(a->fg, afn);
        struct Etat etat_fd = arbre_vers_afn(a->fd, afn);

        afn[etat_fg.arrivee][0] = '@';
        afn[etat_fg.arrivee][1] = etat_fd.debut;

        etat.debut = etat_fg.debut;
        etat.arrivee = etat_fd.arrivee;
    }
    else if (a->val == '|') {
        struct Etat etat_fg = arbre_vers_afn(a->fg, afn);
        struct Etat etat_fd = arbre_vers_afn(a->fd, afn);

        afn[i][0] = '@';
        afn[i][1] = etat_fg.debut;
        afn[i][2] = etat_fd.debut;

        afn[etat_fg.arrivee][0] = '@';
        afn[etat_fg.arrivee][1] = i + 1;

        afn[etat_fd.arrivee][0] = '@';
        afn[etat_fd.arrivee][1] = i + 1;

        etat.debut = i;
        etat.arrivee = i + 1;

        i += 2;
    }
    else if (a->val == '*') {
        Arbin f = a->fd == NULL ? a->fg : a->fd;

        struct Etat etat_f = arbre_vers_afn(f, afn);

        afn[i][0] = '@';
        afn[i][1] = etat_f.debut;
        afn[i][1] = i + 1;

        afn[etat_f.arrivee][0] = '@';
        afn[etat_f.arrivee][1] = i + 1;
        afn[etat_f.arrivee][2] = etat_f.debut;

        etat.debut = i;
        etat.arrivee = i + 1;

        i += 2;
    }

    return etat;
}

void afficher_afn(int** afn, int nb_etats, struct Etat etats_afn) {
    printf("AFN : l'état initial est %i\n", etats_afn.debut);
    for (int i = 0; i < nb_etats; ++i) {
        printf("Etat : %i ", i);
        if (i == etats_afn.arrivee) {
            printf("FINAL ");
        }
        if (afn[i][1] != -1) {
            printf("--%c--> %i", afn[i][0], afn[i][1]);
        }
        if (afn[i][2] != -1) {
            printf(", --%c--> %i", afn[i][0], afn[i][1]);
        }
        printf("\n");
    }
}

void suppr_afn(int** afn, int nb_etats) {
    for (int i = 0; i < nb_etats; ++i) {
        free(afn[i]);
    }
    free(afn);
}