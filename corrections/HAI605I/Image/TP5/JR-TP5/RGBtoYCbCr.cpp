#include <cstdlib>
#include <stdio.h>

#include "image_ppm.h"

#define R(index) index*3
#define G(index) index*3 + 1
#define B(index) index*3 + 2

int main(int argc, char **argv) {
    // Gestion des arguments. On veut l'image en RGB et les 3 composantes.
    if (argc != 5) {
        printf("Utilisation: %s img_input.ppm img_y.pgm img_cb.pgm img_cr.pgm\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Lecture
    int rows, cols;
    lire_nb_lignes_colonnes_image_ppm(argv[1], &rows, &cols);
    int size = rows * cols;

    OCTET *inputImg;
    allocation_tableau(inputImg, OCTET, rows * cols * 3);

    lire_image_ppm(argv[1], inputImg, size);

    printf("Lecture de %s réussie.\n", argv[1]);

    // Création des 3 tableaux : Y / Cb / Cr
    OCTET *Y, *Cb, *Cr;
    allocation_tableau(Y, OCTET, size);
    allocation_tableau(Cb, OCTET, size);
    allocation_tableau(Cr, OCTET, size);

    // Lecture de l'image
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;

            Y[index] = 0.299*inputImg[R(index)] + 0.587*inputImg[G(index)] + 0.114*inputImg[B(index)];
            Cb[index] = -0.1687*inputImg[R(index)] - 0.3313*inputImg[G(index)] + 0.5*inputImg[B(index)] + 128;
            Cr[index] = 0.5*inputImg[R(index)] - 0.4187*inputImg[G(index)] - 0.0813*inputImg[B(index)] + 128;
        }
    }

    // Enregistrement de Y.pgm, Cb.pgm et Cr.pgm
    ecrire_image_pgm(argv[2], Y, rows, cols); ecrire_image_pgm(argv[3], Cb, rows, cols); ecrire_image_pgm(argv[4], Cr, rows, cols);
    printf("Écriture de %s, %s et %s réussies.\n", argv[2], argv[3], argv[4]);
    free(inputImg); free(Y); free(Cb); free(Cr);
    return 0;
}