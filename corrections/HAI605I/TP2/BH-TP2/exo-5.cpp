#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void erosion(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    int facteur = color ? 3 : 1;
    int boucle = color ? 3 : 1;

    for (int i = 0; i < nH; i++) {
        for (int j = 0; j < nW; j++) {
            for (int k = 0; k < boucle; k++) {
                int M = 0;
                for (int y = max(i - 1, 0); y <= min(i + 1, nH - 1); y++) {
                    for (int x = max(j - 1, 0); x <= min(j + 1, nW - 1); x++) {
                        M = max(M, (int) ImgIn[facteur*(y*nW+x) + k]);
                    }
                }
                ImgOut[facteur*(i*nW+j) + k] = M;
            }
        }
    }
}

void dilatation(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    int facteur = color ? 3 : 1;
    int boucle = color ? 3 : 1;

    for (int i = 0; i < nH; i++) {
        for (int j = 0; j < nW; j++) {
            for (int k = 0; k < boucle; k++) {
                int m = 255;
                for (int y = max(i - 1, 0); y <= min(i + 1, nH - 1); y++) {
                    for (int x = max(j - 1, 0); x <= min(j + 1, nW - 1); x++) {
                        m = min(m, (int) ImgIn[facteur*(y*nW+x) + k]);
                    }
                }
                ImgOut[facteur*(i*nW+j) + k] = m;
            }
        }
    }
}

void fermeture(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    OCTET *ImgTemp;
    allocation_tableau(ImgTemp, OCTET, nW * nH * (color ? 3 : 1));

    dilatation(ImgIn, ImgTemp, nH, nW, color);
    erosion(ImgTemp, ImgOut, nH, nW, color);

    free(ImgTemp);
}

void ouverture(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    OCTET *ImgTemp;
    allocation_tableau(ImgTemp, OCTET, nW * nH * (color ? 3 : 1));

    erosion(ImgIn, ImgTemp, nH, nW, color);
    dilatation(ImgTemp, ImgOut, nH, nW, color);

    free(ImgTemp);
}

void difference(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    OCTET *ImgEro;
    OCTET *ImgDil;
    allocation_tableau(ImgEro, OCTET, nW * nH * (color ? 3 : 1));
    allocation_tableau(ImgDil, OCTET, nW * nH * (color ? 3 : 1));

    erosion(ImgIn, ImgEro, nH, nW, color);
    dilatation(ImgIn, ImgDil, nH, nW, color);

    int S = 235;

    for (int i = 0; i < nW * nH * (color ? 3 : 1); ++i) {
        int val = 255 - (abs(ImgDil[i] - ImgEro[i]))/2;
        ImgOut[i] = (val < S ? 0 : 255);
    }

    free(ImgEro);
    free(ImgDil);
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    char cNomImgEcrite[250];
    int nH, nW, nTaille;
    
    if (argc != 4) {
        printf("Usage: ImageIn.p(gp)m ImageOut.p(gp)m Type\n"); 
        exit(1);
    }
    
    sscanf(argv[1],"%s",cNomImgLue);
    sscanf(argv[2],"%s",cNomImgEcrite);

    char ext[4] = "ppm";
    bool color = strcmp(cNomImgLue + strlen(cNomImgLue) - 3, ext) == 0;

    OCTET *ImgIn, *ImgOut;
    
    if (color)  lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
    else        lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);

    nTaille = color ? nH * nW * 3 : nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    allocation_tableau(ImgOut, OCTET, nTaille);

    if (color)  lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    else        lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    
    switch (atoi(argv[3])) {
        case 1:
            erosion(ImgIn, ImgOut, nH, nW, color);
            break;
        case 2:
            dilatation(ImgIn, ImgOut, nH, nW, color);
            break;
        case 3:
            fermeture(ImgIn, ImgOut, nH, nW, color);
            break;
        case 4:
            ouverture(ImgIn, ImgOut, nH, nW, color);
            break;
        case 5:
            difference(ImgIn, ImgOut, nH, nW, color);
            break;
        default:
            printf("Param type doit être 1: erosion, 2: dilatation, 3: fermeture, 4: ouverture, 5: difference");
            break;
    }

    if (color)  ecrire_image_ppm(cNomImgEcrite, ImgOut, nH, nW);
    else        ecrire_image_pgm(cNomImgEcrite, ImgOut, nH, nW);

    free(ImgIn);
    free(ImgOut);

    return 1;
}
