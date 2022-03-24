// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
    char cNomImgLue1[250];
    char cNomImgLue2[250];
    char cNomImgEcrite[250];
    int nH, nW, nTaille;
    
    if (argc != 4) {
        printf("Usage: ImageIn1.pgm ImageIn2.pgm ImageOut.pgm\n"); 
        exit(1) ;
    }
    
    sscanf(argv[1],"%s",cNomImgLue1);
    sscanf(argv[2],"%s",cNomImgLue2);
    sscanf(argv[3],"%s",cNomImgEcrite);

    OCTET *ImgIn1, *ImgIn2, *ImgOut;
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue1, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn1, OCTET, nTaille);
    allocation_tableau(ImgIn2, OCTET, nTaille);
    lire_image_pgm(cNomImgLue1, ImgIn1, nH * nW);
    lire_image_pgm(cNomImgLue2, ImgIn2, nH * nW);
    allocation_tableau(ImgOut, OCTET, nTaille);
    
    for (int i = 0; i < nH; i++) {
        for (int j = 0; j < nW; j++) {
            if (ImgIn1[i*nW+j] == ImgIn2[i*nW+j]) {
                ImgOut[i*nW+j] = 255;
            }
            else {
                ImgOut[i*nW+j] = 0;
            }
        }
    }

    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn1);
    free(ImgIn2);
    free(ImgOut);

    return 1;
}
