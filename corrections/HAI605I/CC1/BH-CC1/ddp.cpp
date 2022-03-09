#include <cmath>
#include <cstring>
#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void ddp(OCTET* ImgIn, int nH, int nW) {
    int nb_pixel[255];
    double ddp[255];

    for (int i = 0; i < 255; ++i) {
        nb_pixel[i] = 0;
    }

    for (int i = 0; i < nH * nW; ++i) {
        nb_pixel[ImgIn[i]]++;
    }

    for (int i = 0; i < 255; ++i) {
        ddp[i] = nb_pixel[i] / ((double) nH * nW);
    }

    printf("couleur ddp\n");
    for (int i = 0; i < 255; ++i) {
        printf("%i %f\n", i, ddp[i]);
    }
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    int nH, nW;
    OCTET *ImgIn;

    sscanf(argv[1],"%s",cNomImgLue);
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    allocation_tableau(ImgIn, OCTET, nH * nW);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);

    ddp(ImgIn, nH, nW);
    free(ImgIn);
    return 0;
}
