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
	
   //   for (int i=0; i < nTaille; i++)
   // {
   //  if ( ImgIn[i] < S) TxtOut[i]=0; else TxtOut[i]=255;
   //  }

    int TxtOut[256] = {0};
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
        fprintf(file_output, "%d\t%d\n", i, TxtOut[i]);
    }
    fclose(file_output);
   free(ImgIn);

   return 1;
}