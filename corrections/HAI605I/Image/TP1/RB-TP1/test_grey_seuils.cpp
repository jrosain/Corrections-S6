/*
Author: Robin Boanca
Date: 10/02/2022
*/


// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
    char cNomImgLue[250], cNomImgEcrite[250];
    int nH, nW, nTaille, nb_seuil, s1, s2, s3;
    
    if (argc < 5) 
        {
        printf("Usage: ImageIn.pgm ImageOut.pgm nbSeuils[1-3] seuil1 [seuil2] [seuil3]\n"); 
        exit (1) ;
        }
    
    sscanf (argv[1],"%s",cNomImgLue) ;
    sscanf (argv[2],"%s",cNomImgEcrite);
    sscanf (argv[3],"%d",&nb_seuil);
    sscanf (argv[4],"%d",&s1);
    if (nb_seuil > 1) sscanf(argv[5],"%d",&s2);
    if (nb_seuil > 2) sscanf(argv[6],"%d",&s3);


    OCTET *ImgIn, *ImgOut;
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(ImgOut, OCTET, nTaille);

    for (int i=0; i < nH; i++) {
        for (int j=0; j < nW; j++)
        {
            if (nb_seuil == 1) {
                if (ImgIn[i*nW+j] < s1) {
                    ImgOut[i*nW+j]=0; 
                } else { 
                    ImgOut[i*nW+j]=255;
                }
            } else if(nb_seuil == 2) {
                if (ImgIn[i*nW+j] < s1) {
                    ImgOut[i*nW+j]=0; 
                } else if(ImgIn[i*nW+j] < s2) { 
                    ImgOut[i*nW+j]=128;
                } else {
                    ImgOut[i*nW+j]=255;
                }
            } else if(nb_seuil == 3) {
                if (ImgIn[i*nW+j] < s1) {
                    ImgOut[i*nW+j]=0; 
                } else if(ImgIn[i*nW+j] < s2) { 
                    ImgOut[i*nW+j]=85;
                } else if(ImgIn[i*nW+j] < s3) { 
                    ImgOut[i*nW+j]=170;
                } else {
                    ImgOut[i*nW+j]=255;
                }
            }
        }
    }

    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn); free(ImgOut);

    return 1;
}