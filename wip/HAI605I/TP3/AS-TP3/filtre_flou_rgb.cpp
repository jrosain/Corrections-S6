#include <cstdlib>
#include <stdio.h>
#include "image_ppm.h"
using namespace std;

int blurR(OCTET* img,int i,int j, int nH, int nW) {
  return  ( img[((i-1)*nW+(j-1))*3]+img[((i)*nW+(j-1))*3]+img[((i+1)*nW+(j-1))*3]+
            img[((i-1)*nW+(j))*3]+img[((i)*nW+(j))*3]+img[((i+1)*nW+(j))*3]+
            img[((i-1)*nW+(j+1))*3]+img[((i)*nW+(j+1))*3]+img[((i+1)*nW+(j+1))*3])/9;
}

int blurG(OCTET* img,int i,int j, int nH, int nW) {
  return  ( img[((i-1)*nW+(j-1))*3+1]+img[((i)*nW+(j-1))*3+1]+img[((i+1)*nW+(j-1))*3+1]+
            img[((i-1)*nW+(j))*3+1]+img[((i)*nW+(j))*3+1]+img[((i+1)*nW+(j))*3+1]+
            img[((i-1)*nW+(j+1))*3+1]+img[((i)*nW+(j+1))*3+1]+img[((i+1)*nW+(j+1))*3+1])/9;
}

int blurB(OCTET* img,int i,int j, int nH, int nW) {
  return  ( img[((i-1)*nW+(j-1))*3+2]+img[((i)*nW+(j-1))*3+2]+img[((i+1)*nW+(j-1))*3+2]+
            img[((i-1)*nW+(j))*3+2]+img[((i)*nW+(j))*3+2]+img[((i+1)*nW+(j))*3+2]+
            img[((i-1)*nW+(j+1))*3+2]+img[((i)*nW+(j+1))*3+2]+img[((i+1)*nW+(j+1))*3+2])/9;
}


int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomImgEcrite[250];
  int nH, nW, nTaille;

  if (argc != 3) 
     {
       printf("Usage: ImageIn.ppm ImageOut.ppm\n"); 
       exit (1) ;
     }
   
   sscanf (argv[1],"%s",cNomImgLue) ;
   sscanf (argv[2],"%s",cNomImgEcrite);

   OCTET *ImgIn;
   OCTET *ImgOut;

   lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
   nTaille = (nH * nW) *3;
  
   allocation_tableau(ImgIn, OCTET, nTaille);
   allocation_tableau(ImgOut, OCTET, nTaille);
   lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    for (int i=0; i < nH; i++) {
        for (int j=0; j < nW; j++)
        {
            if (i == 0 || j == 0 || i == nH-1 || j == nW-1) {
                ImgOut[(i*nW+j)*3] = ImgIn[(i*nW+j)*3];
                ImgOut[(i*nW+j)*3+1] = ImgIn[(i*nW+j)*3+1];
                ImgOut[(i*nW+j)*3+2] = ImgIn[(i*nW+j)*3+2];
            }
            else {
                ImgOut[(i*nW+j)*3] = blurR(ImgIn, i, j, nH, nW) ;
                ImgOut[(i*nW+j)*3+1] = blurG(ImgIn, i, j, nH, nW) ;
                ImgOut[(i*nW+j)*3+2] = blurB(ImgIn, i, j, nH, nW) ;
            }
        }
    }
    ecrire_image_ppm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn);
    free(ImgOut);
   return 1;
}