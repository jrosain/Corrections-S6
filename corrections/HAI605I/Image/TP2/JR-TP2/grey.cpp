#include <cmath>
#include <cstdlib>
#include <stdio.h>

#include "image_ppm.h"

#define MAX 255
#define ERROR -1

OCTET* read_and_allocate_pgm(char *inputImgName, int *rows, int *cols) {
    // Récupération du nombre de lignes / colonnes de l'image d'entrée.
    lire_nb_lignes_colonnes_image_pgm(inputImgName, rows, cols);
    int size = *rows * *cols;

    // Allocation du tableaux d'octets pour la lecture de l'image
    OCTET *inputImg;
    allocation_tableau(inputImg, OCTET, size);

    // Lecture de l'image entrée dans le tableau d'octet correpondant
    lire_image_pgm(inputImgName, inputImg, size);

    return inputImg;
}

void erode(OCTET *inputImg, OCTET *outputImg, int rows, int cols) {
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            // Vérification des voisins : en haut à gauche & en bas à droite.
            // Élément structurant de 3 pixels.
            int max = 0;
            for (int k = -1; k < 2; ++k) {
                for (int m = -1; m < 2; ++m) {
                    if (m == 0 && k == 0) {
                        continue;
                    }
                    
                    int id = (i+k) * cols + (j + m);
                    if (id >= 0 && id < rows * cols) {
                        max = (inputImg[id] > max) ? inputImg[id] : max;
                    }
                }
            }
            int index = i*cols + j;
            outputImg[index] = max;
        }
    }
}

void dilatate(OCTET *inputImg, OCTET *outputImg, int rows, int cols) {
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            // Vérification des voisins : en haut à gauche & en bas à droite.
            // Élément structurant de 3 pixels.
            int min = MAX;
            for (int k = -1; k < 2; ++k) {
                for (int m = -1; m < 2; ++m) {
                    if (m == 0 && k == 0) {
                        continue;
                    }

                    int id = (i+k) * cols + (j + m);
                    if (id >= 0 && id < rows * cols) {
                        min = (inputImg[id] < min) ? inputImg[id] : min;
                    }
                }
            }
            int index = i*cols + j;
            outputImg[index] = min;
        }
    }
}

// Érosion d'une image pgm 
void exo1(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // Érosion
    erode(inputImg, outputImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Dilatation d'une image pgm 
void exo2(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // Dilatation
    dilatate(inputImg, outputImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Fermeture (dilatation + érosion) d'une image pgm
void fermeture(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *dilatedImg;
    allocation_tableau(dilatedImg, OCTET, rows * cols);
    dilatate(inputImg, dilatedImg, rows, cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *erodedImg;
    allocation_tableau(erodedImg, OCTET, rows * cols);
    erode(dilatedImg, erodedImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, erodedImg, rows, cols);
    free(inputImg); free(dilatedImg); free(erodedImg);
}

// Ouverture (érosion + dilatation) d'une image pgm
void ouverture(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *erodedImg;
    allocation_tableau(erodedImg, OCTET, rows * cols);
    erode(inputImg, erodedImg, rows, cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *dilatedImg;
    allocation_tableau(dilatedImg, OCTET, rows * cols);
    dilatate(erodedImg, dilatedImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, dilatedImg, rows, cols);
    free(inputImg); free(dilatedImg); free(erodedImg);
}

// 3 dilatations + 6 érosions + 3 dilatations
void exo3d(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // 3 Dilatations
    dilatate(inputImg, outputImg, rows, cols);
    dilatate(outputImg, inputImg, rows, cols);
    dilatate(inputImg, outputImg, rows, cols);

    // 6 Érosions
    erode(outputImg, inputImg, rows, cols);
    erode(inputImg, outputImg, rows, cols);
    erode(outputImg, inputImg, rows, cols);
    erode(inputImg, outputImg, rows, cols);
    erode(outputImg, inputImg, rows, cols);
    erode(inputImg, outputImg, rows, cols);

    // 3 Dilatations
    dilatate(outputImg, inputImg, rows, cols);
    dilatate(inputImg, outputImg, rows, cols);
    dilatate(outputImg, inputImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, inputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Différence
void exo4(char *binaryImgName, char *dilatedImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *binaryImg = read_and_allocate_pgm(binaryImgName, &rows, &cols);
    OCTET *dilatedImg = read_and_allocate_pgm(dilatedImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // Différence
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            if (binaryImg[index] == dilatedImg[index]) {
                outputImg[index] = MAX;
            }
        }
    }

    ecrire_image_pgm(outputImgName, outputImg, rows, cols);
    free(binaryImg); free(dilatedImg); free(outputImg);
}

// Différence d'une image non binaire
void exo5(char *erodedImgName, char *dilatedImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *erodedImg = read_and_allocate_pgm(erodedImgName, &rows, &cols);
    OCTET *dilatedImg = read_and_allocate_pgm(dilatedImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // Différence
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            outputImg[index] = ceil(abs(erodedImg[index] - dilatedImg[index]) / 2);
        }
    }

    ecrire_image_pgm(outputImgName, outputImg, rows, cols);
    free(erodedImg); free(dilatedImg); free(outputImg);
}

int main(int argc, char **argv) {
    if (argc < 2) {
        printf("Utilisation : %s exercice {options}\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    int exercise = atoi(argv[1]);

    if (exercise < 1 || exercise > 6) {
        printf("Utilisation : %s exercice (1 <= exercice <= 6) {options}\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    switch (exercise) {
    case 1:
        if (argc != 4) {
            printf("Utilisation : %s 1 image_entree.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo1(argv[2], argv[3]);
        break;
    case 2:
        if (argc != 4) {
            printf("Utilisation : %s 2 image_entree.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo2(argv[2], argv[3]);
        break;
    case 3:
        if (argc != 5) {
            printf("Utilisation : %s 3 {a|b|c|d|e} image_entree.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        if (argv[2][0] == 'a') {
            fermeture(argv[3], argv[4]);
        }
        else if (argv[2][0] == 'b') {
            ouverture(argv[3], argv[4]);
        }
        else if (argv[2][0] == 'c') {
            fermeture(argv[3], argv[4]);
            ouverture(argv[4], argv[4]);
        }
        else if (argv[2][0] == 'd') {
            ouverture(argv[3], argv[4]);
            fermeture(argv[4], argv[4]);
        }
        else {
            exo3d(argv[3], argv[4]);
        }
        break;
    case 4:
        if (argc != 5) {
            printf("Utilisation : %s 4 image_entree_binaire.pgm image_entree_dilatee.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo4(argv[2], argv[3], argv[4]);
        break;
    case 5:
        if (argc != 5) {
            printf("Utilisation : %s 5 image_entree_erodee.pgm image_entree_dilatee.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo5(argv[2], argv[3], argv[4]);
        break;
    }

    return 0;
}
