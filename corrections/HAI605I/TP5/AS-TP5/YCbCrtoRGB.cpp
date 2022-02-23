#include <cstdlib>
#include <stdio.h>
#include "image_ppm.h"
#include <string>
using namespace std;

int main(int argc, char* argv[]) {
    char cNomImgOut[250], cNomImgY[250], cNomImgCb[250], cNomImgCr[250];
    int nH, nW, nTaille, nTailleRGB;

    if (argc != 5) 
        {
        printf("Usage: ImageOut.ppm ImageInY.pgm ImageInCb.pgm ImageInCr.pgm\n"); 
        exit (1) ;
        }

    sscanf (argv[1],"%s",cNomImgOut);
    sscanf (argv[2],"%s",cNomImgY) ;
    sscanf (argv[3],"%s",cNomImgCb) ;
    sscanf (argv[4],"%s",cNomImgCr) ;

    OCTET *ImgInY;
    OCTET *ImgInCb;
    OCTET *ImgInCr;
    OCTET *ImgOut;


    lire_nb_lignes_colonnes_image_pgm(cNomImgY, &nH, &nW);
    nTaille = nH * nW;
    nTailleRGB = (nH * nW) * 3;
    //printf("Nom images lues : %s - %s - %s\n", ImgInY, ImgInCb, ImgInCr);
    printf("Largeur : %i, Hauteur %i\n", nW, nH);

    allocation_tableau(ImgInY, OCTET, nTaille);
    allocation_tableau(ImgInCb, OCTET, nTaille);
    allocation_tableau(ImgInCr, OCTET, nTaille);
    allocation_tableau(ImgOut, OCTET, nTailleRGB);
    lire_image_pgm(cNomImgY, ImgInY, nH * nW);
    lire_image_pgm(cNomImgCb, ImgInCb, nH * nW);
    lire_image_pgm(cNomImgCr, ImgInCr, nH * nW);

        for (int i=0; i < nH; i++) {
            for (int j=0; j < nW; j++) {
                ImgOut[(i*nW+j)*3] =  ImgInY[(i*nW+j)] + 1.402 * (ImgInCr[(i*nW+j)] - 128);
                ImgOut[(i*nW+j)*3+1] = ImgInY[(i*nW+j)] - 0.34414 * (ImgInCb[(i*nW+j)] - 128) - 0.714414 * (ImgInCr[(i*nW+j)] -128);
                ImgOut[(i*nW+j)*3+2] = ImgInY[(i*nW+j)] + 1.402 * (ImgInCb[(i*nW+j)] - 128);
            }
        }
        ecrire_image_ppm(cNomImgOut, ImgOut,  nH, nW);
        free(ImgInY);
        free(ImgInCb);
        free(ImgInCr);
        free(ImgOut);
        
    return 1;
}