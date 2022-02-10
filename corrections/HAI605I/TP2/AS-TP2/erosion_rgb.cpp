// test_couleur.cpp : Seuille une image en niveau de gris

#include <stdio.h>
#include "image_ppm.h"

int main(int argc, char* argv[])
{
  char cNomImgLue[250], cNomImgEcrite[250];
  int nH, nW, nTaille, R_min, G_min, B_min;
  
  if (argc != 3) 
     {
       printf("Usage: ImageIn.ppm ImageOut.ppm\n"); 
       exit (1) ;
     }
   
   sscanf (argv[1],"%s",cNomImgLue) ;
   sscanf (argv[2],"%s",cNomImgEcrite);

   OCTET *ImgIn, *ImgOut;
   
   lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
   nTaille = (nH * nW) * 3;
  
   allocation_tableau(ImgIn, OCTET, nTaille);
   lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
   allocation_tableau(ImgOut, OCTET, nTaille);

    for (int i=1; i < nH-1; i++) {
        for (int j=1; j < nW-1; j++) {
            R_min = 255;
            G_min = 255;
            B_min = 255;

            if(ImgIn[((i-1)*nW+(j-1))*3] < R_min) {R_min = ImgIn[((i-1)*nW+(j-1))*3];} 
            if(ImgIn[((i-1)*nW+j)*3] < R_min) {R_min = ImgIn[((i-1)*nW+j)*3];} 
            if(ImgIn[((i-1)*nW+(j+1))*3] < R_min) {R_min = ImgIn[((i-1)*nW+(j+1))*3];} 
            if(ImgIn[((i)*nW+(j-1))*3] < R_min) {R_min = ImgIn[((i)*nW+(j-1))*3];}  
            if(ImgIn[((i)*nW+(j))*3] < R_min) {R_min = ImgIn[((i)*nW+(j))*3];} 
            if(ImgIn[((i)*nW+(j+1))*3] < R_min) {R_min = ImgIn[((i)*nW+(j+1))*3];}  
            if(ImgIn[((i+1)*nW+(j-1))*3] < R_min) {R_min = ImgIn[((i+1)*nW+(j-1))*3];} 
            if(ImgIn[((i+1)*nW+j)*3] < R_min) {R_min = ImgIn[((i+1)*nW+j)*3];} 
            if(ImgIn[((i+1)*nW+(j+1))*3] < R_min) {R_min = ImgIn[((i+1)*nW+(j+1))*3];} 

            if(ImgIn[((i-1)*nW+(j-1))*3+1] < G_min) {G_min = ImgIn[((i-1)*nW+(j-1))*3+1];} 
            if(ImgIn[((i-1)*nW+j)*3+1] < G_min) {G_min = ImgIn[((i-1)*nW+j)*3+1];} 
            if(ImgIn[((i-1)*nW+(j+1))*3+1] < G_min) {G_min = ImgIn[((i-1)*nW+(j+1))*3+1];} 
            if(ImgIn[((i)*nW+(j-1))*3+1] < G_min) {G_min = ImgIn[((i)*nW+(j-1))*3+1];}  
            if(ImgIn[((i)*nW+(j))*3+1] < G_min) {G_min = ImgIn[((i)*nW+(j))*3+1];} 
            if(ImgIn[((i)*nW+(j+1))*3+1] < G_min) {G_min = ImgIn[((i)*nW+(j+1))*3+1];}  
            if(ImgIn[((i+1)*nW+(j-1))*3+1] < G_min) {G_min = ImgIn[((i+1)*nW+(j-1))*3+1];} 
            if(ImgIn[((i+1)*nW+j)*3+1] < G_min) {G_min = ImgIn[((i+1)*nW+j)*3+1];} 
            if(ImgIn[((i+1)*nW+(j+1))*3+1] < G_min) {G_min = ImgIn[((i+1)*nW+(j+1))*3+1];} 

            if(ImgIn[((i-1)*nW+(j-1))*3+2] < B_min) {B_min = ImgIn[((i-1)*nW+(j-1))*3+2];} 
            if(ImgIn[((i-1)*nW+j)*3+2] < B_min) {B_min = ImgIn[((i-1)*nW+j)*3+2];} 
            if(ImgIn[((i-1)*nW+(j+1))*3+2] < B_min) {B_min = ImgIn[((i-1)*nW+(j+1))*3+2];} 
            if(ImgIn[((i)*nW+(j-1))*3+2] < B_min) {B_min = ImgIn[((i)*nW+(j-1))*3+2];}  
            if(ImgIn[((i)*nW+(j))*3+2] < B_min) {B_min = ImgIn[((i)*nW+(j))*3+2];} 
            if(ImgIn[((i)*nW+(j+1))*3+2] < B_min) {B_min = ImgIn[((i)*nW+(j+1))*3+2];}  
            if(ImgIn[((i+1)*nW+(j-1))*3+2] < B_min) {B_min = ImgIn[((i+1)*nW+(j-1))*3+2];} 
            if(ImgIn[((i+1)*nW+j)*3+2] < B_min) {B_min = ImgIn[((i+1)*nW+j)*3+2];} 
            if(ImgIn[((i+1)*nW+(j+1))*3+2] < B_min) {B_min = ImgIn[((i+1)*nW+(j+1))*3+2];} 
            
            ImgOut[(i*nW+j)*3]=R_min;
            ImgOut[(i*nW+j)*3+1]=G_min;
            ImgOut[(i*nW+j)*3+2]=B_min;
        }
    }

   ecrire_image_ppm(cNomImgEcrite, ImgOut,  nH, nW);
   free(ImgIn); free(ImgOut);

   return 1;
}