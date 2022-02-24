#include <cstdlib>
#include <stdio.h>

#include "image_ppm.h"

int main(int argc, char **argv) {
    // Gestion des arguments : on veut les 2 images à comparer
    if (argc != 3) {
        printf("Utilisation: %s image_auto.pgm image_manu.pgm\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);

    int size = rows * cols;

    // Lecture des deux images.
    OCTET *imgAuto, *imgMan;
    allocation_tableau(imgAuto, OCTET, size);
    allocation_tableau(imgMan, OCTET, size);

    lire_image_pgm(argv[1], imgAuto, size);
    lire_image_pgm(argv[2], imgMan, size);

    // Comparaison
    double EQM = 0;
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            EQM += pow(imgAuto[index] - imgMan[index], 2);
        }
    }
    printf("EQM: %f\n", EQM/(rows*cols));
    return 0;
} 