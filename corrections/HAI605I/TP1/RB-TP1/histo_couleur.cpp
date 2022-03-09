/*
Author: Robin Boanca
Date: 10/02/2022
*/


// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    int nH, nW, nTaille;
    
    if (argc != 2) 
        {
        printf("Usage: ImageIn.pgm \n"); 
        exit (1) ;
        }
    
    sscanf (argv[1],"%s",cNomImgLue) ;

    OCTET *ImgIn;
    int *HistoR, *HistoG, *HistoB;
    int maxGris = 256;

    lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    int nTaille3 = nTaille * 3;
    allocation_tableau(ImgIn, OCTET, nTaille3);
    lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(HistoR, int, maxGris);
    allocation_tableau(HistoG, int, maxGris);
    allocation_tableau(HistoB, int, maxGris);

    // lecture - comptage des niveaux de gris
    for(int i=0; i<nTaille3; i+=3) {
        HistoR[ImgIn[i]]++;
        HistoG[ImgIn[i+1]]++;
        HistoB[ImgIn[i+2]]++;
    }
    //enregistrement des résultats
    for(int i=1; i<maxGris-1; i++) {
        printf("%i %i %i %i\n",i,HistoR[i],HistoG[i],HistoB[i]);
    }

    free(ImgIn); 
    free(HistoR);
    free(HistoG);
    free(HistoB);
    
    return 1;
}
