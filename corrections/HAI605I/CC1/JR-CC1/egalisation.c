#include <stdio.h>

#include "image_ppm.h"

#define MAX 255
#define ERROR -1

int main(int argc, char **argv) {
    if (argc < 2 || argc > 3) {
        printf("Utilisation : %s image_entree.pgm image_sortie.pgm\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);
    int size = rows * cols;

    OCTET *inputImg, *outputImg;
    allocation_tableau(inputImg, OCTET, size);
    allocation_tableau(outputImg, OCTET, size);

    lire_image_pgm(argv[1], inputImg, size);

    // Instancier un tableau de niveaux, tout à 0.
    int *histo;
    allocation_tableau(histo, int, MAX + 1);

    // Comptage du nombre de pixels de niveau i pour i allant de 0 à 255.
    // levels[0] équivaut au nombre de pixels qui ont un niveau de gris = 0 et ainsi de suite.
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            ++histo[inputImg[i*cols + j]];
        }
    }

    double *ddp;
    allocation_tableau(ddp, double, MAX + 1);
    double *F;
    allocation_tableau(F, double, MAX + 1);
    for (int i = 0; i < MAX + 1; ++i) {
        ddp[i] = ((double)histo[i])/size;
        if (i == 0)
            F[i] = ddp[i];
        else 
            F[i] = F[i - 1] + ddp[i];
    }

    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            outputImg[index] = F[inputImg[index]] * 255;
            printf("outputImg[index] = %f, inputImg[index] = %i, outputImg[index] = %i\n", F[inputImg[index]] * 255, inputImg[index], outputImg[index]);
        }
    }

    ecrire_image_pgm(argv[2], outputImg, rows, cols);

    // Désallocation de la mémoire.
    free(inputImg); free(ddp); free(outputImg); free(histo); free(F); 
}