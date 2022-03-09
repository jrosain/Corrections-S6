/**
 * fichier: modifY.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
#include <stdio.h>
#include <stdlib.h>

#include "image_ppm.h"

#define min(a,b) (a < b ? a : b)
#define max(a,b) (a >= b ? a : b)

int main(int argc, char **argv) {
    // Gestion des arguments : on veut la composante Y d'entrée et la composante Y de sortie
    if (argc != 4) {
        printf("Utilisation: %s composante_Y.pgm composante_Y_modifiee.pgm k\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    int k = atoi(argv[3]);

    // Lecture de Y 
    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);

    int size = rows * cols;

    OCTET *Y, *Ymodif;
    allocation_tableau(Y, OCTET, size);
    allocation_tableau(Ymodif, OCTET, size);

    lire_image_pgm(argv[1], Y, size);
    printf("Image lue: %s\n", argv[1]);

    // Modification de Y
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            Ymodif[index] = max(0, min(255, Y[index] + k));
        }
    }

    // Écriture dans le fichier
    ecrire_image_pgm(argv[2], Ymodif, rows, cols);
    free(Y); free(Ymodif);

    printf("Image écrite: %s\n", argv[2]);
    return 0;
}