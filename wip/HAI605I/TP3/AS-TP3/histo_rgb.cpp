// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"
using namespace std;

int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomTxtEcrite[250];
  int nH, nW, nTaille;
  
  if (argc != 3) 
     {
       printf("Usage: ImageIn.pgm histoRGB.dat\n"); 
       exit (1) ;
     }
   
   sscanf (argv[1],"%s",cNomImgLue) ;
   sscanf (argv[2],"%s",cNomTxtEcrite);


   OCTET *ImgIn;
   
   lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
   nTaille = nH * nW;
  
   int nTaille3 = nTaille * 3;
   allocation_tableau(ImgIn, OCTET, nTaille3);
   lire_image_ppm(cNomImgLue, ImgIn, nH * nW);

    int TxtOutR[256] = {0};
    int TxtOutG[256] = {0};
    int TxtOutB[256] = {0};
    FILE* file_output;
    if((file_output = fopen(cNomTxtEcrite,"w")) == NULL) {
        exit(EXIT_FAILURE);
    };

    int nR, nG, nB =0;
    for (int i=0; i < nTaille3; i+=3)
    {
      nR = ImgIn[i];
      nG = ImgIn[i+1];
      nB = ImgIn[i+2];
      TxtOutR[nR]++;
      TxtOutG[nG]++;
      TxtOutB[nB]++;

    }

    for (int i = 0; i < 256; i++) {
        fprintf(file_output, "%d\t%d\t%d\t%d\n", i, TxtOutR[i], TxtOutG[i], TxtOutB[i]);
    }

    fclose(file_output);
    free(ImgIn);

   return 1;
}