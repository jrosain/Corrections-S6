//Pour seuiller une image pgm (que du noir et du blanc)
#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomImgEcrite[250];
  int nH, nW, nTaille;
  
  if (argc != 3) 
    {
      printf("Usage: ImageIn.pgm ImageOut.pgm \n"); 
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
  float TxtOut[256] = {0};

  for (int i=0; i < nH; i++)
    for (int j=0; j < nW; j++)
      {
          TxtOut[ImgIn[i*nW+j]]++;
      }
      for (int i = 0; i < 256; i++) {
          if (i == 0) {
            TxtOut[i] = float(TxtOut[i])/float(nTaille);
          }
          else {
              TxtOut[i] = TxtOut[i-1] + float(TxtOut[i])/float(nTaille);
          }
      }
  for (int i=0; i < nH; i++)
    for (int j=0; j < nW; j++)
      {
        ImgOut[i*nW+j] = floor(TxtOut[ImgIn[i*nW+j]]*255);
      }
  ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
  free(ImgIn); free(ImgOut);

  return 1;
}