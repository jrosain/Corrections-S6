// Donne les valeurs pour l'histogramme en nuances de gris (Nombre de pixels par valeur de gris)
#include <stdio.h>
#include "image_ppm.h"
using namespace std;

int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomTxtEcrite[250];
  int nH, nW, nTaille;
  
  if (argc != 3) 
    {
      printf("Usage: ImageIn.pgm ImageOut.dat\n"); 
      exit (1) ;
    }
  
  sscanf (argv[1],"%s",cNomImgLue) ;
  sscanf (argv[2],"%s",cNomTxtEcrite);


  OCTET *ImgIn;

  lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
  nTaille = nH * nW;
  
  allocation_tableau(ImgIn, OCTET, nTaille);
  lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
  
  float TxtOut[256] = {0};
  FILE* file_output;
  if((file_output = fopen(cNomTxtEcrite,"w")) == NULL) {
      exit(EXIT_FAILURE);
  };
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
          fprintf(file_output, "%d\t%f\n", i, TxtOut[i]);
      }
    fclose(file_output);
  free(ImgIn);

  return 1;
}