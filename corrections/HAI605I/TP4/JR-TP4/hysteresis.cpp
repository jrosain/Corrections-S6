#include <cstdlib>
#include <stdio.h>

#include "image_ppm.h"

int main(int argc, char **argv) {
    // Traitement des arguments 
    if (argc != 5) {
        printf("Utilisation: %s image_entree.pgm image_sortie.pgm seuil_bas seuil_haut\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    int sb = atoi(argv[3]);
    int sh = atoi(argv[4]);

    // Lecture de la taille l'image d'entrée
    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);

    int size = rows * cols;

    // Allocation
    OCTET *inputImg, *preseuil, *seuil;
    allocation_tableau(inputImg, OCTET, size);
    allocation_tableau(preseuil, OCTET, size);
    allocation_tableau(seuil, OCTET, size);

    // Lecture de l'image d'entrée
    lire_image_pgm(argv[1], inputImg, size);

    // Pré-seuillage
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            if (inputImg[index] <= sb)
                preseuil[index] = 0;
            else if (inputImg[index] >= sh)
                preseuil[index] = 255;
            else 
                preseuil[index] = inputImg[index];
        }
    }

    // Vrai seuillage
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            if (preseuil[index] != 0 && preseuil[index] != 255) {
                int found = 0;
                for (int k = -1; k <= 1; ++k) {
                    for (int m = -1; m <= 1; ++m) {
                        int id = (i + k)*cols + (j + m);
                        if (0 >= id && id < size && preseuil[id] == 255) {
                            found = 1;
                        }
                    }
                }
                seuil[index] = 255 * found;
            }
            else 
                seuil[index] = preseuil[index];
        }
    }

    // Enregistrement dans la sortie
    ecrire_image_pgm(argv[2], seuil, rows, cols);
    free(inputImg); free(preseuil); free(seuil);
    return 0;
}