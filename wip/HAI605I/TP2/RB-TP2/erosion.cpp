
#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
    char cNomImgLue[250], cNomImgEcrite[250];
    int nH, nW, nTaille;
    
    if (argc != 3) 
        {
        printf("Usage: ImageIn.pgm ImageOut.pgm\n"); 
        exit (1) ;
        }
    
    sscanf (argv[1],"%s",cNomImgLue) ;
    sscanf (argv[2],"%s",cNomImgEcrite);

    OCTET *ImgIn, *ImgOut;
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(ImgOut, OCTET, nTaille);

    for (int i=0; i < nH; i++) { 
        for (int j=0; j < nW; j++) {
            int pixelVal = 0;
            if (ImgIn[i*nW+j] == 0) { //si le pixel est noir (sinon pas la peine)
                for(int a=-1; a<2; a++) {
                    for(int b=-1; b<2; b++){
                        if (a!=0 || b!=0) { //on ne regarde pas le pixel central
                            if(i+a >=0 && i+a < nH && j+b >=0 && j+b < nW) { //on ne dépasse pas des bords
                                if(ImgIn[(a+i)*nW+j+b] == 255) {
                                    pixelVal = 255;
                                } 
                            } 
                        } 
                    } 
                } 
            } else {
                pixelVal = 255;
            }
            ImgOut[i*nW+j] = pixelVal;             
        }
    } 

    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn); free(ImgOut);

    return 1;
}
