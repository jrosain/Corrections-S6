// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    char cNomImgEcrite[250];
    int nH, nW, nTaille;
    int S;
    
    if (argc != 4) {
        printf("Usage: ImageIn.pgm ImageOut.pgm Seuil\n"); 
        exit(1) ;
    }
    
    sscanf(argv[1],"%s",cNomImgLue);
    sscanf(argv[2],"%s",cNomImgEcrite);
    sscanf(argv[3],"%d",&S);

    OCTET *ImgIn, *ImgOut;
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(ImgOut, OCTET, nTaille);
    
    for (int i = 0; i < nTaille; i++) {
        if (ImgIn[i] < S) {
            ImgOut[i] = 0;
        }
        else {
            ImgOut[i] = 255;
        }
    }

    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn);
    free(ImgOut);

    return 1;
}
