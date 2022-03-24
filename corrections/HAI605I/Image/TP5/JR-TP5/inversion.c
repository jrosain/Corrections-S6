/**
 * fichier: inversion.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
#include <stdio.h>
#include <stdlib.h>

#include "image_ppm.h"

#define R(index) index*3
#define G(index) index*3 + 1
#define B(index) index*3 + 2
#define min(a,b) (a < b ? a : b)
#define max(a,b) (a >= b ? a : b)

enum Inversion {
    BlueIsGreen,
    RedIsBlueAndGreenIsRed,
    BlueIsRed,
    RedIsGreen,
    RedIsGreenAndRedIsBlue,
};

int main(int argc, char **argv) {
    // Gestion des arguments : 3 composantes (Y, Cb, Cr) et sort une image en format ppm
    if (argc != 6) {
        printf("Utilisation: %s Y.pgm Cb.pgm Cr.pgm sortie.ppm nombre_inversion\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    int num_inversion = atoi(argv[5]);

    // Allocation des 3 images
    int rows, cols;
    // Les 3 images ont la même taille !
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);
    int size = rows * cols;

    OCTET *Y, *Cb, *Cr;
    allocation_tableau(Y, OCTET, size);
    allocation_tableau(Cb, OCTET, size);
    allocation_tableau(Cr, OCTET, size);

    // Lecture des 3 composantes
    lire_image_pgm(argv[1], Y, size);
    lire_image_pgm(argv[2], Cb, size);
    lire_image_pgm(argv[3], Cr, size);

    printf("Composantes Y Cb Cr lues correctement.\n");

    // Création du tableau de sortie
    OCTET *out;
    allocation_tableau(out, OCTET, size * 3);

    // Écriture dans la composante RGB
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            int r = Y[index] + 1.402*(Cr[index] - 128);
            int g = Y[index] - 0.34414*(Cb[index] - 128) - 0.714414*(Cr[index] - 128);
            int b = Y[index] + 1.772*(Cb[index] - 128);

            switch (num_inversion) {
            case BlueIsGreen:
                out[R(index)] = max(0, min(255, r));
                out[G(index)] = max(0, min(255, b));
                out[B(index)] = max(0, min(255, g));
                break;
            case RedIsBlueAndGreenIsRed:
                out[R(index)] = max(0, min(255, b));
                out[G(index)] = max(0, min(255, r));
                out[B(index)] = max(0, min(255, g));
                break;
            case BlueIsRed:
                out[R(index)] = max(0, min(255, b));
                out[G(index)] = max(0, min(255, g));
                out[B(index)] = max(0, min(255, r));
                break;
            case RedIsGreen:
                out[R(index)] = max(0, min(255, g));
                out[G(index)] = max(0, min(255, r));
                out[B(index)] = max(0, min(255, b));
                break;
            case RedIsGreenAndRedIsBlue:
                out[R(index)] = max(0, min(255, g));
                out[G(index)] = max(0, min(255, b));
                out[B(index)] = max(0, min(255, r));
                break;
            default :
                out[R(index)] = max(0, min(255, r));
                out[G(index)] = max(0, min(255, g));
                out[B(index)] = max(0, min(255, b));
            }
        }
    }

    // Écriture de l'image
    ecrire_image_ppm(argv[4], out, rows, cols);
    free(out); free(Y); free(Cr); free(Cb);
    printf("Écriture dans %s réussie.\n", argv[4]);
    return 0;
}