#include <cstdlib>
#include <stdio.h>
#include "image_ppm.h"
using namespace std;



int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomImgEcrite[250];
  int nH, nW, nTaille, nTailleGrey;

  if (argc != 3) 
    {
      printf("Usage: ImageIn.ppm ImageOut.pgm\n"); 
      exit (1) ;
    }
  
  sscanf (argv[1],"%s",cNomImgLue) ;
  sscanf (argv[2],"%s",cNomImgEcrite);

  OCTET *ImgIn;
  OCTET *ImgOut;

  lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
  nTaille = (nH * nW) *3;
  nTailleGrey = (nH * nW);
  printf("Nom image lue : %s",cNomImgLue);
  printf("Largeur : %i, Hauteur %i\n", nW, nH);

  allocation_tableau(ImgIn, OCTET, nTaille);
  allocation_tableau(ImgOut, OCTET, nTailleGrey);
  lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    for (int i=0; i < nH; i++) {
      for (int j=0; j < nW; j++) {
          ImgOut[(i*nW+j)] = (ImgIn[(i*nW+j)*3] + ImgIn[(i*nW+j)*3+1] + ImgIn[(i*nW+j)*3+2])/3;
      }
    }
    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn);
    free(ImgOut);
  return 1;
}