// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"


bool voisin_good(OCTET* img,int i,int j, int nH, int nW) {
  if (i == 0 || i == nH-1 || j == 0 || j == nW-1) {return false;}
  if (img[(i-1)*nW+(j-1)] == 255) return true;
  if (img[(i)*nW+(j-1)] == 255) return true;
  if (img[(i+1)*nW+(j-1)] == 255) return true;
  if (img[(i-1)*nW+(j)] == 255) return true;
  if (img[(i)*nW+(j)] == 255) return true;
  if (img[(i+1)*nW+(j)] == 255) return true;
  if (img[(i-1)*nW+(j+1)] == 255) return true;
  if (img[(i)*nW+(j+1)] == 255) return true;
  if (img[(i+1)*nW+(j+1)] == 255) return true;
  return false;
}

int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomImgEcrite[250];
  int nH, nW, nTaille, SB, SH;
  
  if (argc != 5) 
     {
       printf("Usage: ImageIn.pgm ImageOut.pgm Seuil_bas Seuil_haut \n"); 
       exit (1) ;
     }
   
   sscanf (argv[1],"%s",cNomImgLue) ;
   sscanf (argv[2],"%s",cNomImgEcrite);
   sscanf (argv[3],"%d",&SB);
   sscanf (argv[4],"%d",&SH);

   OCTET *ImgIn, *ImgOut;
   
   lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
   nTaille = nH * nW;
  
   allocation_tableau(ImgIn, OCTET, nTaille);
   lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
   allocation_tableau(ImgOut, OCTET, nTaille);
	
   //   for (int i=0; i < nTaille; i++)
   // {
   //  if ( ImgIn[i] < S) ImgOut[i]=0; else ImgOut[i]=255;
   //  }

  //premier seuilage
  for (int i=0; i < nH; i++) {
    for (int j=0; j < nW; j++) {
        if (ImgIn[i*nW+j] < SH) {ImgOut[i*nW+j]=0;} 
        else {ImgOut[i*nW+j]=255;}
    }
  }

  //second seuilage
  for (int i=0; i < nH; i++) {
    for (int j=0; j < nW; j++) {
        if ((ImgOut[i*nW+j] > SB) && voisin_good(ImgOut,i,j,nH,nW)) {
          ImgOut[i*nW+j]=255;
        }
        else {ImgOut[i*nW+j]=0;}
    }
  }

   ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
   free(ImgIn); free(ImgOut);

   return 1;
}

