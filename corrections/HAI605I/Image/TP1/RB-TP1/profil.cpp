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
    char cColLine[15];
    int nH, nW, nTaille, indice;
    
    if (argc != 4) 
        {
        printf("Usage: ImageIn.pgm [Line|Col] indice\n"); 
        exit (1) ;
        }
    
    sscanf (argv[1],"%s",cNomImgLue) ;
    sscanf (argv[2],"%s",cColLine) ;
    sscanf (argv[3],"%d",&indice) ;

    if (strcmp(cColLine, "col") && strcmp(cColLine, "line")) {
        printf("écrire <<col>> ou <<line>>\n");
        exit(1);
    }

    OCTET *ImgIn;
    int *Histo;
    int maxGris = 65536;

    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(Histo, int, maxGris);

    int maxiCoul = 0;
    // lecture - comptage des niveaux de gris
    if (strcmp(cColLine, "col") == 0) {
        for(int y=0; y<nH; y++) {
            Histo[ImgIn[indice + y*nW]]++;
            if (ImgIn[indice + y*nW] > maxiCoul) {
                maxiCoul = ImgIn[indice + y*nW];
            }
        }
    } else {
        for(int x=0; x<nH; x++) {
            Histo[ImgIn[indice*nW + x]]++;
            if (ImgIn[indice*nW + x] > maxiCoul) {
                maxiCoul = ImgIn[indice*nW + x];
            }
        }
    }
    //enregistrement des résultats
    for(int i=0; i<=maxiCoul; i++) {
        printf("%i %i\n",i,Histo[i]);
    }

    free(ImgIn); 
    free(Histo);
    
    return 1;
}
