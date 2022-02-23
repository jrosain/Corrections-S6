#include <cstdlib>
#include <stdio.h>
#include "image_ppm.h"
#include <string>
using namespace std;

int main(int argc, char* argv[]) {
    char cNomImgY[250], cNomImgOut[250];
    int nH, nW, nTaille, K;

    if (argc != 3) 
        {
        printf("Usage: ImageInY.pgm K-param\n"); 
        exit (1) ;
        }

    sscanf ("Ymodif.pgm","%s",cNomImgOut);
    sscanf (argv[1],"%s",cNomImgY) ;
    K = atoi(argv[2]);

    while(K > 128 || K < -128) {
        printf("K doit être compris entre -128 et 128\n K = ");
        scanf("%d", &K);
    }
    OCTET *ImgInY;
    OCTET *ImgOut;


    lire_nb_lignes_colonnes_image_pgm(cNomImgY, &nH, &nW);
    nTaille = nH * nW;
    printf("Largeur : %i, Hauteur %i\n", nW, nH);

    allocation_tableau(ImgInY, OCTET, nTaille);
    allocation_tableau(ImgOut, OCTET, nTaille);
    lire_image_pgm(cNomImgY, ImgInY, nH * nW);

        for (int i=0; i < nH; i++) {
            for (int j=0; j < nW; j++) {
                if (ImgInY[(i*nW+j)] + K > 255) {
                    ImgOut[(i*nW+j)] = 255;
                }
                else if (ImgInY[(i*nW+j)] - K < 0) {
                    ImgOut[(i*nW+j)] = 0;
                }
                else {
                    ImgOut[(i*nW+j)] =  ImgInY[(i*nW+j)] + K ;
                }
                
            }
        }
        ecrire_image_pgm(cNomImgOut, ImgOut,  nH, nW);
        free(ImgInY);
        free(ImgOut);
        
    return 1;
}