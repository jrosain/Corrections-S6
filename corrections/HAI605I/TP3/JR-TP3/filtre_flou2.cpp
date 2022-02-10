#include <cstdlib>

#include "image_ppm.h"

int main(int argc, char **argv) {
    if (argc != 3) {
        printf("Utilisation : %s image_entree.pgm image_sortie.pgm\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Lecture de l'image d'entrée
    //  1 - Lignes / colonnes 
    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);

    //  2 - Allouer les tableaux de l'image d'entrée et sortie
    OCTET *inputImg, *outputImg;
    allocation_tableau(inputImg, OCTET, rows * cols);
    allocation_tableau(outputImg, OCTET, rows * cols);

    //  3 - Lecture des pixels de l'image pgm d'entrée dans le tableau correspondant
    lire_image_pgm(argv[1], inputImg, rows * cols);

    // Flouter
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;

            if (i == 0 || j == 0 || i == rows - 1 || j == cols - 1) {
                outputImg[index] = inputImg[index];
            }
            else {
                int sum = 0;

                for (int k = -1; k <= 1; ++k) {
                    for (int m = -1; m <= 1; ++m) {
                        int key = (i + k)*cols + (j + m);
                        sum += inputImg[key];
                    }
                }

                outputImg[index] = round(sum / 9);
            }
        }
    }

    // Écriture dans l'image de sortie
    ecrire_image_pgm(argv[2], outputImg, rows, cols);

    // Libération de la mémoire
    free(inputImg); free(outputImg);

    // C'est fini !
    printf("Image floutée : %s\n", argv[2]);
    return 0;
}