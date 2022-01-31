#include <cmath>
#include <cstdlib>
#include <stdio.h>

#include "image_ppm.h"

#define MAX 255
#define ERROR -1
#define R 0
#define G 1
#define B 2

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

// Seuillage d'une image pgm avec un seul niveau (exercice 1)
void exo1(char *inputImgName, char *outputImgName, int threshold) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // Seuillage
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;
            // Si c'est <, comme l'allocation a tout mis à 0, on n'a pas besoin de le préciser.
            if (inputImg[index] >= threshold) {
                outputImg[index] = MAX;
            }
        }
    }

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Seuillage d'une image pgm avec 2 ou 3 niveaux (exercice 2)
void exo2(char *inputImgName, char *outputImgName, int *thresholds, size_t len) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    // Création des différents niveaux de gris.
    int levels[len];
    levels[0] = 0;
    for (size_t i = 1; i < len; ++i) {
        levels[i] = round((thresholds[i - 1] + thresholds[i]) / 2);
    }

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols);

    // Seuillage
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int index = i*cols + j;

            // On cherche le premier seuil avec un niveau supérieur à celui du pixel actuel 
            size_t k = 0;
            while (k < len && inputImg[index] >= thresholds[k])
                k++;

            // Si on n'en trouve pas, c'est que son niveau est supérieur au seuil maximal, donc on le met à 255.
            if (k == len) {
                outputImg[index] = MAX;
            }
            // Sinon, on le met au seuil trouvé. levels[0] == 0.
            else {
                outputImg[index] = levels[k];
            }
        }
    }

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_pgm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Construction de l'histogramme d'une image pgm
void exo3(char *inputImgName, const char *outputDataFile) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

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
        if (fprintf(dataFd, "%i %i\n", i, levels[i]) == ERROR) {
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

// Profilage de la k-ème ligne ou de la k-ième colonne. 
void exo4(char *inputImgName, int k, int isRow, const char *outputDataFile) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_pgm(inputImgName, &rows, &cols);

    if ((isRow && rows < k) || (!isRow && cols < k)) {
        printf("Erreur : l'indice demandé de la ligne ou de la colonne est trop grand.\n");
        exit(EXIT_FAILURE);
    }

    // Instancier un tableau de niveaux, tout à 0.
    int *levels;
    allocation_tableau(levels, int, MAX + 1);

    // Comptage du nombre de pixels de niveau i pour i allant de 0 à 255.
    // levels[0] équivaut au nombre de pixels qui ont un niveau de gris = 0 et ainsi de suite.
    if (isRow) {
        // k-ème ligne et on parcours les colonnes -> k*cols + i
        for (int i = 0; i < cols; ++i) {
            ++levels[inputImg[k*cols + i]];
        }
    } 
    else {
        // k-ème colonne et on parcours les lignes -> i*cols + k
        for (int i = 0; i < rows; ++i) {
            ++levels[inputImg[i*cols + k]];
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
        if (fprintf(dataFd, "%i %i\n", i, levels[i]) == ERROR) {
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

// Seuillage d'une image ppm (RGB)
void exo5(char *inputImgName, char *outputImgName, int red, int green, int blue) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_ppm(inputImgName, &rows, &cols);

    // Allocation à part, on ne peut pas l'allouer dans read_and_allocate car le pointeur est remplacé.
    OCTET *outputImg;
    allocation_tableau(outputImg, OCTET, rows * cols * 3);

    // Tableau des seuils pour faciliter le travail dans la boucle.
    int thresholds[3] = { red, green, blue };

    // Seuillage
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int k = j * 3;
            int key = i*cols*3 + k;

            // Chaque pixel est codé sur 3 octets : rouge, vert, bleu (dans cet ordre).
            // On parcours donc ces 3 octets et on regarde si le seuillage est à faire.
            for (int color = R; color <= B; ++color) {
                if (inputImg[key + color] < thresholds[color]) {
                    outputImg[key + color] = 0;
                } else {
                    outputImg[key + color] = MAX;
                }
            }

        }
    }

    // Écriture de l'image en fichier & fin de la fonction.
    ecrire_image_ppm(outputImgName, outputImg, rows, cols);
    free(inputImg); free(outputImg);
}

// Construction de l'histogramme d'une image pgm
void exo6(char *inputImgName, const char *outputDataFile) {
    // Lecture de l'image d'entrée et allocation de la taille mémoire des images.
    int rows, cols;
    OCTET *inputImg = read_and_allocate_ppm(inputImgName, &rows, &cols);

    // Instancier trois tableaux de niveaux, tout à 0.
    int *levelsRed, *levelsGreen, *levelsBlue;
    allocation_tableau(levelsRed, int, MAX + 1);
    allocation_tableau(levelsGreen, int, MAX + 1);
    allocation_tableau(levelsBlue, int, MAX + 1);

    // Comptage du nombre de pixels de niveau i pour i allant de 0 à 255.
    // levels[0] équivaut au nombre de pixels qui ont un niveau de gris = 0 et ainsi de suite.
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            int k = j * 3;
            int key = i * cols * 3 + k;

            ++levelsRed[inputImg[key + R]];
            ++levelsGreen[inputImg[key + G]];
            ++levelsBlue[inputImg[key + B]];
        }
    }

    // Enregistrement dans un fichier histo.dat.
    FILE *dataFd = fopen(outputDataFile, "w");
    if (dataFd == NULL) {
        printf("Erreur : le fichier %s n'a pas pu être ouvert en écriture\n", outputDataFile);
        exit(EXIT_FAILURE);
    }

    fprintf(dataFd, "index red green blue\n");
    // Parcours du tableau par indice. Écriture dans le fichier pour chaque indice.
    for (int i = 0; i < MAX + 1; ++i) {
        if (fprintf(dataFd, "%i %i %i %i\n", i, levelsRed[i], levelsGreen[i], levelsBlue[i]) == ERROR) {
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
    free(inputImg); free(levelsRed); free(levelsGreen); free(levelsBlue);
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
        if (argc != 5) {
            printf("Utilisation : %s 1 image_entree.pgm image_sortie.pgm seuil\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo1(argv[2], argv[3], atoi(argv[4]));
        break;
    case 2: {
        if (argc < 6 || argc > 7) {
            printf("Utilisation : %s 2 image_entree.pgm image_sortie.pgm seuil1 seuil2 [seuil3]\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        // Les 4 premiers arguments ne sont pas des seuils. On compte le reste.
        size_t len = argc - 4;

        // Récupération des différents seuils
        int *thresholds = (int *)malloc(len * sizeof(int));
        for (size_t i = 4; i < 4 + len; ++i) {
            int key = i - 4;
            thresholds[key] = atoi(argv[i]);
            if (thresholds[key] < 0 || thresholds[key] > MAX) {
                printf("Erreur : le niveau de seuillage doit être 0 < niveau < 256.\n");
                exit(EXIT_FAILURE);
            }
        }
        exo2(argv[2], argv[3], thresholds, len);

        // On n'a plus besoin du tableau de seuils
        free(thresholds);
        break;
    }
    case 3:
        if (argc < 3 || argc > 4) {
            printf("Utilisation : %s 3 image_entree.pgm [donnees.dat]\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        // L'utilisateur n'a pas précisé de fichier dans lequel il veut enregistrer les données.
        // Enregistrement automatique dans histo.dat
        if (argc == 3) {
            exo3(argv[2], "histo.dat");
        }
        else {
            exo3(argv[2], argv[3]);
        }
        break;
    case 4: {
        if (argc < 5 || argc > 6) {
            printf("Utilisation : %s 4 image_entree.pgm {c|l} indice [donnees.dat]\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        int isRow = argv[3][0] == 'l';

        // L'utilisateur n'a pas précisé de fichier dans lequel il veut enregistrer les données.
        // Enregistrement automatique dans profil.dat
        if (argc == 5) {
            exo4(argv[2], atoi(argv[4]), isRow, "profil.dat");
        }
        else {
            exo4(argv[2], atoi(argv[4]), isRow, argv[5]);
        }
        break;
    }
    case 5: 
        if (argc != 7) {
            printf("Utilisation : %s 5 image_entree.ppm image_sortie.ppm seuil_rouge seuil_vert seuil_bleu\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        exo5(argv[2], argv[3], atoi(argv[4]), atoi(argv[5]), atoi(argv[6]));
        break;
    case 6:
        if (argc < 3 || argc > 4) {
            printf("Utilisation : %s 6 image_entree.ppm [donnees.dat]\n", argv[0]);
            exit(EXIT_FAILURE);
        }

        // L'utilisateur n'a pas précisé de fichier dans lequel il veut enregistrer les données.
        // Enregistrement automatique dans histo.dat
        if (argc == 3) {
            exo6(argv[2], "histo.dat");
        }
        else {
            exo6(argv[2], argv[3]);
        }
        break;
    }

    return 0;
}
