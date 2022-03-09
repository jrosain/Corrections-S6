/*
Author: Robin Boanca
Date: 17/02/2022
*/

#include <stdio.h>
#include "image_ppm.h"
#include <math.h>

void gradient(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW) {
    int gH, gV;
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            gH = 0;
            gV = 0;
            if(i > 0) {
                gV -= ImgIn[(i-1)*nW + j];
            } else {
                gV -= ImgIn[i*nW + j];
            }
            if(i < nH-1) {
                gV += ImgIn[(i+1)*nW + j];
            } else {
                gV += ImgIn[i*nW + j];
            }
            if(j > 0) {
                gH -= ImgIn[i*nW + j-1];
            } else {
                gH -= ImgIn[i*nW + j];
            }
            if(j < nW-1) {
                gH += ImgIn[i*nW + j+1];
            } else {
                gH += ImgIn[i*nW + j];
            }
            ImgOut[i*nW+j] = sqrt(gV*gV + gH*gH);
        }
    }
}

void profil(OCTET* ImgIn, int nH, int nW, int ligne) {
    for(int i=0; i<nW; i++) {
        printf("%i %i\n",i,ImgIn[ligne*nW+i]);
    }
}

void seuillage(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, int seuil) {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int val = ImgIn[i*nW+j];
            int ret = 0;
            if(val >= seuil) {
                ret = 255;
            }
            ImgOut[i*nW+j] = ret;
        }
    }
}

void hysteresis(OCTET* ImgIn, OCTET* ImgInter, OCTET* ImgOut, int nH, int nW, int seuilBas, int seuilHaut) {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int val = ImgIn[i*nW+j];
            int ret = 0;
            if(val >= seuilHaut) {
                ret = 255;
            }
            ImgInter[i*nW+j] = ret;
        }
    }
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int valInter = ImgInter[i*nW+j];
            int valIn = ImgIn[i*nW+j];
            int ret = valInter;
            if(valInter == 0 && valIn >= seuilBas) {
                for(int a=-1; a<2; a++) {
                    for(int b=-1; b<2; b++) {
                        if(i+a>=0 && i+a<nH && j+b>=0 && j+b<nW) {
                            if(ImgInter[(i+a)*nW+j+b] == 255) {
                                ret = 255;
                            }
                        }
                    }
                }
            }
            ImgOut[i*nW+j] = ret;
        }
    }
}

void moyenneur(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW) {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int somme = 0;
            int quantite = 0;
            for(int a=-1; a<2; a++) {
                for(int b=-1; b<2; b++) {
                    if(i+a>=0 && i+a<nH && j+b>=0 && j+b<nW) {
                        somme += ImgIn[(i+a)*nW+j+b];
                        quantite++;
                    }
                }
            }
            ImgOut[i*nW+j] = (int)(somme/quantite);
        }
    }
}

void gaussien(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW) {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int somme = 0;
            int quantite = 0;
            for(int a=-1; a<2; a++) {
                for(int b=-1; b<2; b++) {
                    if(i+a>=0 && i+a<nH && j+b>=0 && j+b<nW) {
                        int mult = 2;
                        if(a==b && a==0) {
                            mult = 4;
                        } else if(a==b || a==-b) {
                            mult = 1;
                        }
                        somme += mult * ImgIn[(i+a)*nW+j+b];
                        quantite += mult;
                    }
                }
            }
            ImgOut[i*nW+j] = (int)(somme/quantite);
        }
    }
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250], cNomImgEcrite[250], option[50];
    int nH, nW, nTaille, val1, val2;
    
    if (argc < 4) {
        printf("Usage: ImageIn.pgm ImageOut.pgm -[(g)radient|(p)rofil|(s)euil|(h)ysteresis|(m)oyenneur|g(a)ussien] [optVal1] [optVal2]\n"); 
        exit (1) ;
    }
    
    sscanf(argv[1],"%s",cNomImgLue) ;
    sscanf(argv[2],"%s",cNomImgEcrite);
    sscanf(argv[3],"%s",option);

    if(option[1] == 's' || option[1] == 'h' || option[1] == 'p') {
        sscanf(argv[4],"%d",&val1);
        if(option[1] == 'h') {
            sscanf(argv[5],"%d",&val2);
        }
    }

    OCTET *ImgIn, *ImgInter, *ImgOut;
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(ImgOut, OCTET, nTaille);
    allocation_tableau(ImgInter, OCTET, nTaille);

    if(option[1] == 'g') {
        gradient(ImgIn, ImgOut, nW, nH);
    } else if(option[1] == 'p') {
        profil(ImgIn, nW, nH, val1);
    } else if(option[1] == 's') {
        seuillage(ImgIn, ImgOut, nW, nH, val1);
    } else if(option[1] == 'h') {
        hysteresis(ImgIn, ImgInter, ImgOut, nH, nW, val1, val2);
    } else if(option[1] == 'm') {
        printf("moyenneur\n");
        moyenneur(ImgIn, ImgOut, nH, nW);
    } else if(option[1] == 'a') {
        printf("gaussien\n");
        gaussien(ImgIn, ImgOut, nH, nW);
    }

    if(option[1] != 'p') ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn); free(ImgOut);

    return 1;
}