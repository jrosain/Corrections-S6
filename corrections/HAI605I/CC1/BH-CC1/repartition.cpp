#include <cmath>
#include <cstring>
#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void repartition(OCTET* ImgIn, int nH, int nW) {
    int nb_pixel[255];
    double ddp[255];
    double f[255];

    for (int i = 0; i < 255; ++i) {
        nb_pixel[i] = 0;
    }

    for (int i = 0; i < nH * nW; ++i) {
        nb_pixel[ImgIn[i]]++;
    }

    for (int i = 0; i < 255; ++i) {
        ddp[i] = nb_pixel[i] / ((double) nH * nW);
    }

    f[0] = ddp[0];
    for (int i = 1; i < 255; ++i) {
        f[i] = f[i - 1] + ddp[i];
    }

    printf("couleur répartition\n");
    for (int i = 0; i < 255; ++i) {
        printf("%i %f\n", i, f[i]);
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

    repartition(ImgIn, nH, nW);
    free(ImgIn);
    return 0;
}
