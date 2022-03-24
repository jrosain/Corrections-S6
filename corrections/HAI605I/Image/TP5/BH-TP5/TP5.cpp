#include <cmath>
#include <cstring>
#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void RGBtoY(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW) {
    for (int i = 0; i < nH * nW; ++i) {
        ImgOut[i] = 0.299 * ImgIn[3*i] + 0.587 * ImgIn[3*i + 1] + 0.114 * ImgIn[3*i + 2];
    }
}

void MSE(OCTET* ImgIn1, OCTET* ImgIn2, int nH, int nW, int color) {
    int nb = nH * nW * (color ? 3 : 1);
    int diff = 0;

    for (int i = 0; i < nb; ++i) {
        diff += pow(ImgIn1[i] - ImgIn2[i], 2);
    }

    diff /= nb;
    printf("La différence MSE entre les deux images est %i\n", diff);
}

void RGBtoYCbCr(OCTET* ImgIn, int nH, int nW, char* nom) {
    OCTET *ImgY, *ImgCb, *ImgCr;
    allocation_tableau(ImgY, OCTET, nH * nW);
    allocation_tableau(ImgCb, OCTET, nH * nW);
    allocation_tableau(ImgCr, OCTET, nH * nW);

    int size = strlen(nom);
    char nomY[size + 7];
    char nomCb[size + 8];
    char nomCr[size + 8];

    nomY[0] = nomCb[0] = nomCr[0] = '\0';
    strcat(nomY, nom);
    strcat(nomCb, nom);
    strcat(nomCr, nom);
    strcat(nomY, "-Y.pgm");
    strcat(nomCb, "-Cb.pgm");
    strcat(nomCr, "-Cr.pgm");

    for (int i = 0; i < nH * nW; ++i) {
        ImgY[i]  = 0.299   * ImgIn[3*i] + 0.587  * ImgIn[3*i + 1] + 0.114  * ImgIn[3*i + 2];
        ImgCb[i] = -0.1687 * ImgIn[3*i] - 0.3313 * ImgIn[3*i + 1] + 0.5    * ImgIn[3*i + 2] + 128;
        ImgCr[i] = 0.5     * ImgIn[3*i] - 0.4187 * ImgIn[3*i + 1] - 0.0813 * ImgIn[3*i + 2] + 128;
    }

    ecrire_image_pgm(nomY, ImgY, nH, nW);
    ecrire_image_pgm(nomCb, ImgCb, nH, nW);
    ecrire_image_pgm(nomCr, ImgCr, nH, nW);

    free(ImgY);
    free(ImgCb);
    free(ImgCr);
}

void YCbCrToRGB(OCTET* ImgOut, int nH, int nW, char* nom) {
    OCTET *ImgY, *ImgCb, *ImgCr;
    allocation_tableau(ImgY, OCTET, nH * nW);
    allocation_tableau(ImgCb, OCTET, nH * nW);
    allocation_tableau(ImgCr, OCTET, nH * nW);

    int size = strlen(nom);
    char nomY[size + 7];
    char nomCb[size + 8];
    char nomCr[size + 8];

    nomY[0] = nomCb[0] = nomCr[0] = '\0';
    strcat(nomY, nom);
    strcat(nomCb, nom);
    strcat(nomCr, nom);
    strcat(nomY, "-Y.pgm");
    strcat(nomCb, "-Cb.pgm");
    strcat(nomCr, "-Cr.pgm");

    lire_image_pgm(nomY, ImgY, nH * nW);
    lire_image_pgm(nomCb, ImgCb, nH * nW);
    lire_image_pgm(nomCr, ImgCr, nH * nW);

    for (int i = 0; i < nH * nW; ++i) {
        ImgOut[3*i]     = min(255., max(0., ImgY[i] + 1.402   * (ImgCr[i] - 128)));
        ImgOut[3*i + 1] = min(255., max(0., ImgY[i] - 0.34414 * (ImgCb[i] - 128) - 0.714414 * (ImgCr[i] - 128)));
        ImgOut[3*i + 2] = min(255., max(0., ImgY[i] + 1.772   * (ImgCb[i] - 128)));
    }

    free(ImgY);
    free(ImgCb);
    free(ImgCr);
}

void inversionSpecific(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, const char RGB[3]) {
    int r = RGB[0] == 'R' ? 0 : RGB[0] == 'G' ? 1 : 2;
    int g = RGB[1] == 'R' ? 0 : RGB[1] == 'G' ? 1 : 2;
    int b = RGB[2] == 'R' ? 0 : RGB[2] == 'G' ? 1 : 2;

    for (int i = 0; i < nH * nW; ++i) {
        ImgOut[3*i] = ImgIn[3*i + r];
        ImgOut[3*i + 1] = ImgIn[3*i + g];
        ImgOut[3*i + 2] = ImgIn[3*i + b];
    }
}

void inversion(OCTET* ImgIn, int nH, int nW, char* nom) {
    const char* permutations[6] = { "RGB", "RBG", "GBR", "GRB", "BGR", "BRG" };

    OCTET* ImgOut;
    allocation_tableau(ImgOut, OCTET, nH * nW * 3);
    int size = strlen(nom);
    char nomOut[size + 9];

    for (const char* permutation : permutations) {
        nomOut[0] = '\0';
        strcat(nomOut, nom);
        strcat(nomOut, "-");
        strcat(nomOut, permutation);
        strcat(nomOut, ".ppm");
        inversionSpecific(ImgIn, ImgOut, nH, nW, permutation);
        ecrire_image_ppm(nomOut, ImgOut, nH, nW);
    }

    free(ImgOut);
}

void modify(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, int k) {
    for (int i = 0; i < nH * nW; ++i) {
        ImgOut[i] = min(255, max(0, ImgIn[i] + k));
    }
}

void histogramme_couleur(OCTET* ImgIn, int nH, int nW) {
    int nb_red[255];
    int nb_green[255];
    int nb_blue[255];

    for (int i = 0; i < 255; ++i) {
        nb_red[i] = nb_green[i] = nb_blue[i] = 0;
    }

    for (int i = 0; i < nH * nW; ++i) {
        nb_red[ImgIn[3*i]]++;
        nb_green[ImgIn[3*i + 1]]++;
        nb_blue[ImgIn[3*i + 2]]++;
    }

    // plot for [col=2:4] "histo.dat" using col with lines title columnheader
    printf("nb rouge vert bleu\n");
    for (int i = 0; i < 255; ++i) {
        printf("%i %i %i %i\n", i, nb_red[i], nb_blue[i], nb_green[i]);
    }
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    char cNomImgEcrite[250];
    int nH, nW;
    
    if (argc < 2) {
        printf("Usage: Exo [params selon exo]\n"); 
        exit(1);
    }

    int exo = atoi(argv[1]);

    if (exo <= 0 || exo > 7) {
        printf("Exo %i inconnu\n", exo);
        printf("1: RGB to Y, 2: MSE, 3: RGB to YCbCr, 4: YCrCb to RGB, 5: inversion, 6: modification, 7: histogramme couleur\n");
        exit(1);
    }

    bool needReadInImage = exo != 4;
    bool needWriteOutImage = exo != 3 && exo != 5 && exo != 7;

    char ext[4] = "ppm";
    int color = 0;

    if (needReadInImage) {
        if (argc < 3) {
            printf("L'exo %i demande une image d'entrée pour fonctionner\n", exo);
            exit(1);
        }
        sscanf(argv[2],"%s",cNomImgLue);
        color = strcmp(cNomImgLue + strlen(cNomImgLue) - 3, ext) == 0;
    
        if (color)  lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
        else        lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    }

    if (needWriteOutImage) {
        if (argc < 3 + needReadInImage) {
            printf("L'exo %i demande une image de sortie pour fonctionner\n", exo);
            exit(1);
        }
        sscanf(argv[2 + needReadInImage],"%s",cNomImgEcrite);
        color |= (strcmp(cNomImgEcrite + strlen(cNomImgEcrite) - 3, ext) == 0) << 1;
    }
    
    // On ne connais pas la taille pour cet exo car pas d'entrée
    if (exo == 4) {
        if (argc != 4) {
            printf("Le quatrième paramètre doit être un nom générique pour les 3 images d'entrée qui sont utilisées, elles doivent exister et avoir les noms [nom]-Y.pgm, [nom]-Cb.pgm et [nom]-Cr.pgm\n");
            exit(1);
        }
        char* nom = argv[3];
        char nomY[strlen(nom) + 7];
        nomY[0] = '\0';
        strcat(nomY, nom);
        strcat(nomY, "-Y.pgm");
        lire_nb_lignes_colonnes_image_pgm(nomY, &nH, &nW);
    }
    
    OCTET *ImgIn, *ImgOut;

    if (needReadInImage) {
        allocation_tableau(ImgIn, OCTET, color ? nH * nW * 3 : nH * nW);

        if (color & 1)  lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
        else            lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    }

    if (needWriteOutImage) {
        allocation_tableau(ImgOut, OCTET, color & 2 ? nH * nW * 3 : nH * nW);
    }
    
    switch (exo) {
        case 1:
            if (color != 1) {
                printf("Pour convertir un PPM en PGM il faut que la première image soit une PPM et la seconde une PGM\n");
                exit(1);
            }
            RGBtoY(ImgIn, ImgOut, nH, nW);
            break;
        case 2:
            if (color & 2)  lire_image_ppm(cNomImgEcrite, ImgOut, nH * nW);
            else            lire_image_pgm(cNomImgEcrite, ImgOut, nH * nW);
            MSE(ImgIn, ImgOut, nH, nW, color);
            needWriteOutImage = false;
            free(ImgOut);
            break;
        case 3:
            if (argc != 4) {
                printf("Le quatrième paramètre doit être un nom générique pour les 3 images de sorties qui seront créée\n");
                exit(1);
            }
            if (!(color & 1)) {
                printf("L'image d'entrée doit être une image PPM\n");
                exit(1);
            }
            RGBtoYCbCr(ImgIn, nH, nW, argv[3]);
            break;
        case 4:
            if (!(color & 2)) {
                printf("L'image de sortie doit être une image PPM\n");
                exit(1);
            }
            YCbCrToRGB(ImgOut, nH, nW, argv[3]);
            break;
        case 5:
            if (argc != 4) {
                printf("Le quatrième paramètre doit être un nom générique pour les 6 permutations de sorties qui seront créée\n");
                exit(1);
            }
            if (!(color & 1)) {
                printf("L'image d'entrée doit être une image PPM\n");
                exit(1);
            }
            inversion(ImgIn, nH, nW, argv[3]);
            break;
        case 6: {
            if (argc != 5) {
                printf("Le cinquième paramètre doit être un nombre k tel que -128 < k < 128\n");
                exit(1);
            }
            int k = atoi(argv[4]);
            if (k <= -128 || k >= 128) {
                printf("Le nombre k doit être être entre -128 et 128 non inclus\n");
                exit(1);
            }
            modify(ImgIn, ImgOut, nH, nW, k);
            break;
        }
        case 7:
            if (!color) {
                printf("On attend une image couleur pour l'histogramme\n");
                exit(1);
            }
            histogramme_couleur(ImgIn, nH, nW);
            break;
    }

    if (needWriteOutImage) {
        if (color & 2)  ecrire_image_ppm(cNomImgEcrite, ImgOut, nH, nW);
        else            ecrire_image_pgm(cNomImgEcrite, ImgOut, nH, nW);

        free(ImgOut);
    }

    if (needReadInImage) {
        free(ImgIn);
    }

    return 1;
}
