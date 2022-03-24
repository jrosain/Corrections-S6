#include <cstdlib>
#include <stdio.h>
#include "image_ppm.h"
#include <string>
using namespace std;



int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomImgRed[250], cNomImgGreen[250], cNomImgBlue[250];
  int nH, nW, nTaille, nTailleY;

  if (argc != 2) 
    {
      printf("Usage: ImageIn.ppm \n"); 
      exit (1) ;
    }
  
  sscanf (argv[1],"%s",cNomImgLue) ;
  sscanf ("Cr.pgm","%s",cNomImgRed) ;
  sscanf ("Y.pgm","%s",cNomImgGreen) ;
  sscanf ("Cb.pgm","%s",cNomImgBlue) ;

  OCTET *ImgIn;
  OCTET *ImgOutY;
  OCTET *ImgOutCb;
  OCTET *ImgOutCr;

  lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
  nTaille = (nH * nW) *3;
  nTailleY = nH * nW;
  printf("Nom image lue : %s\n",cNomImgLue);
  printf("Largeur : %i, Hauteur %i\n", nW, nH);

  allocation_tableau(ImgIn, OCTET, nTaille);
  allocation_tableau(ImgOutY, OCTET, nTailleY);
  allocation_tableau(ImgOutCb, OCTET, nTailleY);
  allocation_tableau(ImgOutCr, OCTET, nTailleY);

  lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    for (int i=0; i < nH; i++) {
      for (int j=0; j < nW; j++) {
          ImgOutY[(i*nW+j)] = (0.299 * ImgIn[(i*nW+j)*3] + 0.587 * ImgIn[(i*nW+j)*3+1] + 0.114 * ImgIn[(i*nW+j)*3+2]);
          ImgOutCb[(i*nW+j)] = ((ImgIn[(i*nW+j)*3+2] - ImgOutY[(i*nW+j)]) * 0.564 + 128);
          ImgOutCr[(i*nW+j)] = ((ImgIn[(i*nW+j)*3] - ImgOutY[(i*nW+j)]) * 0.713 + 128);

      }
    }
    ecrire_image_pgm(cNomImgRed, ImgOutCr,  nH, nW);
    ecrire_image_pgm(cNomImgBlue, ImgOutCb,  nH, nW);
    ecrire_image_pgm(cNomImgGreen, ImgOutY,  nH, nW);
    free(ImgIn);
    free(ImgOutY);
    free(ImgOutCb);
    free(ImgOutCr);
  return 1;
}