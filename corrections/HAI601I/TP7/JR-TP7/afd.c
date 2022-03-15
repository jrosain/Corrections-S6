/**
 * fichier: afd.c
 * auteur: Johann Rosain
 * date: 15/03/2022
 **/
#include "afd.h"
#include "arbin.h"

#include <stdlib.h>
#include <stdio.h>

int i = 0;
Pair AFDetats;

int nombreEtats(Arbin a) {
    if (ab_vide(a)) 
        return 0;
    if (ab_racine(a) == '.') 
        return nombreEtats(ab_sag(a)) + nombreEtats(ab_sad(a)); 
    if (ab_racine(a) == '|' || ab_racine(a) == '*') 
        return 2 + nombreEtats(ab_sag(a)) + nombreEtats(ab_sad(a));
    return 2;
}

int **construireAFD(Arbin a) {
    int n = nombreEtats(a);
    int **AFD = (int **)malloc(n * sizeof(int *));
    for (int i = 0; i < n; ++i) {
        AFD[i] = (int *)malloc(3 * sizeof(int));
        AFD[i][0] = AFD[i][1] = -1;
        AFD[i][2] = -1;
    }
    AFDetats = arbreVersAF(a, AFD);
    i = 0;
    return AFD;
}

Pair arbreVersAF(Arbin a, int **AFD) {
    if (ab_vide(a)) return (Pair){-1, -1};
    if (ab_racine(a) == '.') {
        Pair gauche = arbreVersAF(ab_sag(a), AFD);
        Pair droite = arbreVersAF(ab_sad(a), AFD);

        // (arrivée gauche, epsilon, début droite)
        AFD[gauche.arrivee][0] = '@';
        AFD[gauche.arrivee][1] = droite.depart;
        return (Pair){gauche.depart, droite.arrivee};
    } 
    else if (ab_racine(a) == '|') {
        Pair gauche = arbreVersAF(ab_sag(a), AFD);
        Pair droite = arbreVersAF(ab_sad(a), AFD);

        // (i, epsilon, début gauche), (i, epsilon, début droite)
        AFD[i][0] = '@';
        AFD[i][1] = gauche.depart;
        AFD[i][2] = droite.depart;

        // (arrivée gauche, epsilon, i + 1)
        AFD[gauche.arrivee][0] = '@';
        AFD[gauche.arrivee][1] = i + 1;

        // (arrivée droite, epsilon, i + 1)
        AFD[droite.arrivee][0] = '@';
        AFD[droite.arrivee][1] = i + 1;
        i += 2;
        return (Pair){i - 2, i - 1};
    }
    else if (ab_racine(a) == '*') {
        Pair gauche = arbreVersAF(ab_sag(a), AFD);

        // (i, epsilon, début gauche), (i, epsilon, i + 1)
        AFD[i][0] = '@';
        AFD[i][1] = gauche.depart;
        AFD[i][2] = i + 1;

        // (arrivée gauche, epsilon, i + 1), (arrivée gauche, epsilon, début gauche)
        AFD[gauche.arrivee][0] = '@';
        AFD[gauche.arrivee][1] = i + 1;
        AFD[gauche.arrivee][2] = i - 2;
        i += 2;
        return (Pair){i - 2, i - 1};
    }
    else {
        // (i, ab_racine(a), i + 1)
        AFD[i][0] = ab_racine(a);
        AFD[i][1] = i + 1;
        i += 2;
        return (Pair){i - 2, i - 1};
    }
}

void afficherAFD(int **AFD, int nombreEtats) {
    printf("État de départ: %i\n", AFDetats.depart);
    printf("État d'arrivée: %i\n", AFDetats.arrivee);
    for (int i = 0; i < nombreEtats; ++i) {
        if (AFD[i][0] != -1) {
            printf("%i --%c--> %i\n", i, AFD[i][0], AFD[i][1]);
            if (AFD[i][2] != -1) {
                printf("%i --%c--> %i\n", i, AFD[i][0], AFD[i][2]);
            }
        }
    }
}

void libererAFD(int **AFD, int nombreEtats) {
    for (int i = 0; i < nombreEtats; ++i) free(AFD[i]);
    free(AFD);
}