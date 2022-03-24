#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <stdio.h>
#include <cmath>

#include "image_ppm.h"

// Norme des gradients : root(Ix^2 + Iy^2)
int main(int argc, char **argv) {
    // Gestion des paramètres
    if (argc != 3) {
        printf("Utilisation: %s image_entree.pgm image_sortie\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Lecture de la taille l'image d'entrée
    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);

    int size = rows * cols;

    // Allocation
    OCTET *inputImg, *gradientVertical, *gradientHorizontal, *norme;
    allocation_tableau(inputImg, OCTET, size);
    allocation_tableau(gradientVertical, OCTET, size);
    allocation_tableau(gradientHorizontal, OCTET, size);
    allocation_tableau(norme, OCTET, size);

    // Lecture de l'image d'entrée
    lire_image_pgm(argv[1], inputImg, size);

    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int curr = i*cols + j;

            // Gradient vertical
            if (i == rows - 1) {
                gradientVertical[curr] = inputImg[curr];
            }
            else {
                int next = (i + 1) * cols + j;
                gradientVertical[curr] = abs(inputImg[next] - inputImg[curr]);
            }

            // Gradient horizontal
            if (j == cols - 1) {
                gradientHorizontal[curr] = inputImg[curr];
            }
            else {
                int next = curr + 1;
                gradientHorizontal[curr] = abs(inputImg[next] - inputImg[curr]);
            }

            // Norme
            norme[curr] = sqrt(pow(gradientHorizontal[curr], 2) + pow(gradientVertical[curr], 2));
        }
    }


    char *file = argv[2];
    char *filename = (char *)malloc(strlen(file) + 5); // File + .pgm
    char *gradientV = (char *)malloc(strlen(file) + 8); // File + _gv.pgm
    char *gradientH = (char *)malloc(strlen(file) + 8); // File + _gh.pgm

    sprintf(filename, "%s.pgm", file);
    sprintf(gradientV, "%s_gv.pgm", file);
    sprintf(gradientH, "%s_gm.pgm", file);

    ecrire_image_pgm(filename, norme, rows, cols);
    ecrire_image_pgm(gradientV, gradientVertical, rows, cols);
    ecrire_image_pgm(gradientH, gradientHorizontal, rows, cols);

    // Finir proprement
    free(inputImg); free(gradientVertical); free(gradientHorizontal); free(norme); free(filename); free(gradientV); free(gradientH);
    return 0;
}