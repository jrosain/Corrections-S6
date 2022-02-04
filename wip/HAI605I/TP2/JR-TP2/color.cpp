#include <cmath>
#include <cstdlib>
#include <stdio.h>

#include "image_ppm.h"

#define MAX 255
#define ERROR -1
#define R 0
#define G 1
#define B 2

OCTET* read_and_allocate_ppm(char *inputImgName, int *rows, int *cols) {
    // Récupération du nombre de lignes / colonnes de l'image d'entrée.
    lire_nb_lignes_colonnes_image_ppm(inputImgName, rows, cols);
    int size = *rows * *cols;

    // Allocation du tableaux d'octets pour la lecture de l'image
    OCTET *inputImg;
    allocation_tableau(inputImg, OCTET, size * 3);

    // Lecture de l'image entrée dans le tableau d'octet correpondant
    lire_image_ppm(inputImgName, inputImg, size);

    return inputImg;
}

void erode(OCTET *inputImg, OCTET *outputImg, int rows, int cols) {
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            for (int c = R; c <= B; ++c) {
                // Vérification des voisins : en haut à gauche & en bas à droite.
                // Élément structurant de 3 pixels.
                int max = 0;
                for (int k = -1; k <= 1; ++k) {
                    for (int m = -1; m <= 1; ++m) {
                        if (m == 0 && k == 0) {
                            continue;
                        }
                        
                        int id = ((i+k)*cols + (j + m))*3 + c;
                        if (id >= 0 && id < rows * cols * 3) {
                            max = (inputImg[id] > max) ? inputImg[id] : max;
                        }
                    }
                }
                int index = i*cols*3 + j*3 + c;
                outputImg[index] = max;
            }
            
        }
    }
}

void dilatate(OCTET *inputImg, OCTET *outputImg, int rows, int cols) {
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            for (int c = R; c <= B; ++c) {
                // Vérification des voisins : en haut à gauche & en bas à droite.
                // Élément structurant de 3 pixels.
                int min = MAX;
                for (int k = -1; k <= 1; ++k) {
                    for (int m = -1; m <= 1; ++m) {
                        if (m == 0 && k == 0) {
                            continue;
                        }

                        int id = ((i+k) * cols + (j + m))*3 + c;
                        if (id >= 0 && id < rows * cols * 3) {
                            min = (inputImg[id] < min) ? inputImg[id] : min;
                        }
                    }
                }
                int index = i*cols*3 + j*3 + c;
                outputImg[index] = min;
            }

        }
    }
}

// Érosion d'une image pgm 
void exo1(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_ppm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols * 3);

    // Érosion
    erode(inputImg, outputImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_ppm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Dilatation d'une image pgm 
void exo2(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_ppm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols * 3);

    // Dilatation
    dilatate(inputImg, outputImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_ppm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Fermeture (dilatation + érosion) d'une image pgm
void fermeture(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_ppm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *dilatedImg;
    allocation_tableau(dilatedImg, OCTET, rows * cols * 3);
    dilatate(inputImg, dilatedImg, rows, cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *erodedImg;
    allocation_tableau(erodedImg, OCTET, rows * cols * 3);
    erode(dilatedImg, erodedImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_ppm(outputImgName, erodedImg, rows, cols);
    free(inputImg); free(dilatedImg); free(erodedImg);
}

// Ouverture (érosion + dilatation) d'une image pgm
void ouverture(char *inputImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_ppm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *erodedImg;
    allocation_tableau(erodedImg, OCTET, rows * cols * 3);
    erode(inputImg, erodedImg, rows, cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *dilatedImg;
    allocation_tableau(dilatedImg, OCTET, rows * cols * 3);
    dilatate(erodedImg, dilatedImg, rows, cols);

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_ppm(outputImgName, dilatedImg, rows, cols);
    free(inputImg); free(dilatedImg); free(erodedImg);
}

// Différence d'une image non binaire
void exo4(char *erodedImgName, char *dilatedImgName, char *outputImgName) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *erodedImg = read_and_allocate_ppm(erodedImgName, &rows, &cols);
    OCTET *dilatedImg = read_and_allocate_ppm(dilatedImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols * 3);

    // Différence
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols*3 + j*3;
            outputImg[index + R] = ceil(abs(erodedImg[index + R] - dilatedImg[index + R]) / 2);
            outputImg[index + G] = ceil(abs(erodedImg[index + G] - dilatedImg[index + G]) / 2);
            outputImg[index + B] = ceil(abs(erodedImg[index + B] - dilatedImg[index + B]) / 2);
        }
    }

    ecrire_image_ppm(outputImgName, outputImg, rows, cols);
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
            printf("Utilisation : %s 3 {f|o} image_entree.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        if (argv[2][0] == 'f') {
            fermeture(argv[3], argv[4]);
        }
        else {
            ouverture(argv[3], argv[4]);
        }
        break;
    case 4:
        if (argc != 5) {
            printf("Utilisation : %s 4 image_entree_erodee.pgm image_entree_dilatee.pgm image_sortie.pgm\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo4(argv[2], argv[3], argv[4]);
        break;
    }

    return 0;
}
