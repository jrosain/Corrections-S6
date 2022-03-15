
 fichier: afd.h
 auteur: Johann Rosain
 date: 15/03/2022
#include "arbin.h"

typedef struct pair {
    int depart;
    int arrivee;
} Pair;

int nombreEtats(Arbin a);
int **construireAFD(Arbin a);
Pair arbreVersAF(Arbin a, int **AFD);
void afficherAFD(int **AFD, int nombreEtats);
void libererAFD(int **AFD, int nombreEtats);