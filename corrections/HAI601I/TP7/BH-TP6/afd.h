#pragma once

#include "arbin.h"

struct Etat {
    int debut;
    int arrivee;
};

int nombre_etat(Arbin a);
int** creer_afn(Arbin a, int nb_etats);
struct Etat remplir_afn(Arbin a, int** afn);
void afficher_afn(int** afn, int nb_etats, struct Etat etats_afn);
void suppr_afn(int** afn, int nb_etats);