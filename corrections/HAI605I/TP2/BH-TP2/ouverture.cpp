// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    char cNomImgEcrite[250];
    int nH, nW, nTaille;
    
    if (argc != 3) {
        printf("Usage: ImageIn.pgm ImageOut.pgm\n"); 
        exit(1) ;
    }
    
    sscanf(argv[1],"%s",cNomImgLue);
    sscanf(argv[2],"%s",cNomImgEcrite);

    OCTET *ImgIn, *ImgInter, *ImgOut;
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(ImgInter, OCTET, nTaille);
    allocation_tableau(ImgOut, OCTET, nTaille);
    
    for (int i = 0; i < nH; i++) {
        for (int j = 0; j < nW; j++) {
            bool zero = true;
            for (int y = max(i - 1, 0); y <= min(i + 1, nH - 1); y++) {
                for (int x = max(j - 1, 0); x <= min(j + 1, nW - 1); x++) {
                    if (ImgIn[y*nW+x] == 255) {
                        zero = false;
                    }
                }
            }
            if (zero) {
                ImgInter[i*nW+j] = 0;
            }
            else {
                ImgInter[i*nW+j] = 255;
            }
        }
    }
    
    for (int i = 0; i < nH; i++) {
        for (int j = 0; j < nW; j++) {
            bool zero = false;
            for (int y = max(i - 1, 0); y <= min(i + 1, nH - 1); y++) {
                for (int x = max(j - 1, 0); x <= min(j + 1, nW - 1); x++) {
                    if (ImgInter[y*nW+x] == 0) {
                        zero = true;
                    }
                }
            }
            if (zero) {
                ImgOut[i*nW+j] = 0;
            }
            else {
                ImgOut[i*nW+j] = 255;
            }
        }
    }

    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn);
    free(ImgOut);

    return 1;
}
