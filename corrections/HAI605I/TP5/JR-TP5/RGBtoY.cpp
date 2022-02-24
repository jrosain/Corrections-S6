#include <stdio.h>

#include "image_ppm.h"

int main(int argc, char **argv) {
    // Gestion des arguments : on veut une image d'entrée et une image de sortie.
    if (argc != 3) {
        printf("Utilisation: %s image_entree.ppm image_sortie.pgm\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Lecture de l'image d'entrée
    int rows, cols;
    lire_nb_lignes_colonnes_image_ppm(argv[1], &rows, &cols);

    int size = rows * cols;

    OCTET *inputImg;
    allocation_tableau(inputImg, OCTET, size * 3);
    lire_image_ppm(argv[1], inputImg, size);

    printf("Image lue: %s\n", argv[1]);

    // Allocation de l'image de sortie
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, size);

    // Passage en pgm
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = (i*cols) + j;

            outputImg[index] = round((inputImg[index*3] + inputImg[index*3 + 1] + inputImg[index*3 + 2]) / 3); 
        }
    }

    // Enregistrement
    ecrire_image_pgm(argv[2], outputImg, rows, cols);

    printf("Image écrite: %s\n", argv[2]);

    // Désallocation des ressources
    free(inputImg); free(outputImg);
    return 0;
}