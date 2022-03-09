#include <stdio.h>

#include "image_ppm.h"

#define MAX 255
#define ERROR -1

int main(int argc, char **argv) {
    if (argc < 2 || argc > 3) {
        printf("Utilisation : %s image_entree.pgm [donnees.dat]\n", argv[0]);
        exit(EXIT_FAILURE);
    }
    char *outputDataFile = "histo.dat";
    if (argc == 3) outputDataFile = argv[2];

    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    lire_nb_lignes_colonnes_image_pgm(argv[1], &rows, &cols);
    int size = rows * cols;
    OCTET *inputImg;
    allocation_tableau(inputImg, OCTET, size);

    lire_image_pgm(argv[1], inputImg, size);

    // Instancier un tableau de niveaux, tout à 0.
    int *levels;
    allocation_tableau(levels, int, MAX + 1);

    // Comptage du nombre de pixels de niveau i pour i allant de 0 à 255.
    // levels[0] équivaut au nombre de pixels qui ont un niveau de gris = 0 et ainsi de suite.
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            ++levels[inputImg[i*cols + j]];
        }
    }

    // Enregistrement dans un fichier histo.dat.
    FILE *dataFd = fopen(outputDataFile, "w");
    if (dataFd == NULL) {
        printf("Erreur : le fichier %s n'a pas pu être ouvert en écriture\n", outputDataFile);
        exit(EXIT_FAILURE);
    }

    // Parcours du tableau par indice. Écriture dans le fichier pour chaque indice.
    for (int i = 0; i < MAX + 1; ++i) {
        if (fprintf(dataFd, "%i %f\n", i, ((double)levels[i])/size) == ERROR) {
            printf("Erreur : l'écriture dans le fichier %s a échouée\n", outputDataFile);
            exit(EXIT_FAILURE);
        }
    }

    // Fermeture du fichier.
    if (fclose(dataFd) == EOF) {
        perror("Erreur : la fermeture du fichier de données s'est mal passée ");
        exit(EXIT_FAILURE);
    }

    // Désallocation de la mémoire.
    free(inputImg); free(levels);
}