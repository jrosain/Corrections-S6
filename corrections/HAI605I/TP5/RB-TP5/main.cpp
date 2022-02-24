#include <stdio.h>
#include "image_ppm.h"
#include <math.h>

void RGBToY(OCTET* ImgIn, OCTET* ImgOut, int nW, int nH)  {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int pos = 3*(i*nW+j);
            ImgOut[i*nW+j] = (int)((ImgIn[pos] + ImgIn[pos+1] + ImgIn[pos+2])/3);
        }
    }
}

double EQM(OCTET* Img1, OCTET* Img2, int nW, int nH) {
    double somme = 0;
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            somme += (Img1[i*nW+j]-Img2[i*nW+j]) * (Img1[i*nW+j]-Img2[i*nW+j]);
        }
    }
    return sqrt(somme/(nH*nW));
}

void RGBtoYCbCr(OCTET* ImgIn, OCTET* ImgOut, int nW, int nH, int composante) {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int r = ImgIn[3*(i*nW+j)];
            int g = ImgIn[3*(i*nW+j)+1];
            int b = ImgIn[3*(i*nW+j)+2];
            int y = (int)(0 + 0.299*r + 0.587*g + 0.114*b);
            int cb = (int)(128 - 0.1687236*r - 0.331264*g + 0.5*b);
            int cr = (int)(128 + 0.5*r -0.418688*g - 0.081312*b);
            int val;
            if (composante == 1) val = y;
            if (composante == 2) val = cb;
            if (composante == 3) val = cr;
            if (val < 0) val = 0;
            if (val > 255) val = 255;
            ImgOut[i*nW+j] = val;
        }
    }
}

void YCbCrToRGB(OCTET* ImgY, OCTET* ImgCb, OCTET* ImgCr, OCTET* ImgOut, int nW, int nH, int composante=0) {
    for(int i=0; i<nH; i++) {
        for(int j=0; j<nW; j++) {
            int y = ImgY[i*nW+j];
            int cb = ImgCb[i*nW+j];
            int cr = ImgCr[i*nW+j];
            int r = (int)(y + 1.402*(cr-128));
            int g = (int)(y - 0.344136*(cb-128) - 0.714136*(cr-128));
            int b = (int)(y + 1.772*(cb-128));
            if (composante != 0) {
                int inter;
                // the big shuffle
                if (composante == 1) { // RBG
                    inter = g;
                    g = b;
                    b = inter;
                }
                if (composante == 2) { // GRB
                    inter = g;
                    g = r;
                    r = inter;
                }
                if (composante == 3) { // GBR
                    inter = r;
                    r = g;
                    g = b;
                    b = inter;
                }
                if (composante == 4) { // BRG
                    inter = b;
                    b = g;
                    g = r;
                    r = inter;
                }
                if (composante == 5) { // BGR
                    inter = r;
                    r = b;
                    b = inter;
                }
            }
            if (r < 0) r = 0;
            if (r > 255) r = 255;
            if (g < 0) g = 0;
            if (g > 255) g = 255;
            if (b < 0) b = 0;
            if (b > 255) b = 255;
            ImgOut[3*(i*nW+j)] = r;
            ImgOut[3*(i*nW+j)+1] = g;
            ImgOut[3*(i*nW+j)+2] = b;
        }
    }
}

void modify(OCTET* ImgIn, OCTET* ImgOut, int nW, int nH, int k) {
    for (int i=0; i<nW*nH; i++) {
        int val = ImgIn[i];
        val += k;
        if (val < 0) val = 0;
        if (val > 255) val = 255;
        ImgOut[i] = val;
    }
}

void histogrammeCouleur(OCTET* ImgIn, int nW, int nH) {
    int *HistoR, *HistoG, *HistoB;
    int maxGris = 256;
    allocation_tableau(HistoR, int, maxGris);
    allocation_tableau(HistoG, int, maxGris);
    allocation_tableau(HistoB, int, maxGris);
    for(int i=0; i<3*nW*nH; i+=3) {
        HistoR[ImgIn[i]]++;
        HistoG[ImgIn[i+1]]++;
        HistoB[ImgIn[i+2]]++;
    }
    for(int i=1; i<maxGris; i++) {
        printf("%i %i %i %i\n",i,HistoR[i],HistoG[i],HistoB[i]);
    }
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250], cNomImgEcrite[250], option[50];
    int nH, nW, nTaille, val;
    char y[] = "out/y.pgm";
    char cb[] = "out/cb.pgm";
    char cr[] = "out/cr.pgm";
    
    if (argc < 4) {
        printf("Usage: ImageIn.pgm ImageOut.pgm -[(r)gbtoy|(e)qm|(y)cbcr|r(g)bfromycbcr|(s)huffle|(m)odify|(h)istogramme] [optVal1]\n"); 
        exit (1) ;
    }
    
    // scanner les arguments
    sscanf(argv[1],"%s",cNomImgLue) ;
    sscanf(argv[2],"%s",cNomImgEcrite);
    sscanf(argv[3],"%s",option);

    if(option[1] == 'm')
        sscanf(argv[4],"%d",&val);

    OCTET *ImgIn, *ImgInter, *ImgOut, *Img1, *Img2, *Img3;
    
    // lire les dimensions
    if (option[1] == 'r' || option[1] == 'y' || option[1] == 'h') 
        lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
    if (option[1] == 'e' || option[1] == 'g' || option[1] == 's' || option[1] == 'm') 
        lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);

    nTaille = nH * nW;
    int n1 = nTaille;
    int n2 = nTaille;
    int n3 = nTaille;
    if (option[1] == 'r' || option[1] == 'y' || option[1] == 'h') 
        n1 *= 3;
    if (option[1] == 'r' || option[1] == 'g' || option[1] == 's')
        n2 *= 3;
    
    // allouer l'espace
    allocation_tableau(ImgIn, OCTET, n1);
    allocation_tableau(ImgOut, OCTET, n2);
    allocation_tableau(ImgInter, OCTET, n3);
    if (option[1] == 'g' || option[1] == 's') {
        allocation_tableau(Img1, OCTET, n1);
        allocation_tableau(Img2, OCTET, n1);
        allocation_tableau(Img3, OCTET, n1);
    }

    // lire les images
    if (option[1] == 'r' || option[1] == 'y' || option[1] == 'h') 
        lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    if (option[1] == 'e' || option[1] == 'm') {
        lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
        if (option[1] == 'e') {
            lire_image_pgm(cNomImgEcrite, ImgOut, nH * nW);
        }
    }
    if (option[1] == 'g' || option[1] == 's') {
        lire_image_pgm(y, Img1, nH * nW);
        lire_image_pgm(cb, Img2, nH * nW);
        lire_image_pgm(cr, Img3, nH * nW);
    }

    // appels de fonctions
    if (option[1] == 'r') {
        RGBToY(ImgIn, ImgOut, nW, nH);
    }
    if (option[1] == 'e') {
        double res = EQM(ImgIn, ImgOut, nW, nH);
        printf("EQM : %f\n", res);
    }
    if (option[1] == 'y') {
        RGBtoYCbCr(ImgIn, ImgOut, nW, nH, 1);
        ecrire_image_pgm(y, ImgOut, nH, nW);
        RGBtoYCbCr(ImgIn, ImgOut, nW, nH, 2);
        ecrire_image_pgm(cb, ImgOut, nH, nW);
        RGBtoYCbCr(ImgIn, ImgOut, nW, nH, 3);
        ecrire_image_pgm(cr, ImgOut, nH, nW);
    }
    if (option[1] == 'g') {
        YCbCrToRGB(Img1, Img2, Img3, ImgOut, nW, nH);
    }
    if (option[1] == 's') {
        char RBG[] = "out/rbg.ppm";
        char GRB[] = "out/grb.ppm";
        char GBR[] = "out/gbr.ppm";
        char BRG[] = "out/brg.ppm";
        char BGR[] = "out/bgr.ppm";
        YCbCrToRGB(Img1, Img2, Img3, ImgOut, nW, nH, 1);
        ecrire_image_ppm(RBG, ImgOut, nH, nW);
        YCbCrToRGB(Img1, Img2, Img3, ImgOut, nW, nH, 2);
        ecrire_image_ppm(GRB, ImgOut, nH, nW);
        YCbCrToRGB(Img1, Img2, Img3, ImgOut, nW, nH, 3);
        ecrire_image_ppm(GBR, ImgOut, nH, nW);
        YCbCrToRGB(Img1, Img2, Img3, ImgOut, nW, nH, 4);
        ecrire_image_ppm(BRG, ImgOut, nH, nW);
        YCbCrToRGB(Img1, Img2, Img3, ImgOut, nW, nH, 5);
        ecrire_image_ppm(BGR, ImgOut, nH, nW);
    }
    if (option[1] == 'm') {
        modify(ImgIn, ImgOut, nW, nH, val);
    }
    if (option[1] == 'h') {
        histogrammeCouleur(ImgIn, nW, nH);
    }

    // écrire image
    if (option[1] == 'r' || option[1] == 'm')
        ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    if (option[1] == 'g')
        ecrire_image_ppm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn); free(ImgOut); free(ImgInter);

    return 1;
}