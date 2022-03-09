#include <cmath>
#include <cstring>
#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void repartition(OCTET* Img1, OCTET* Img2, int nH, int nW) {
    int nb_pixel_1[255];
    int nb_pixel_2[255];
    double ddp_1[255];
    double ddp_2[255];
    double f_1[255];
    double f_2[255];

    for (int i = 0; i < 255; ++i) {
        nb_pixel_1[i] = nb_pixel_2[i] = 0;
    }

    for (int i = 0; i < nH * nW; ++i) {
        nb_pixel_1[Img1[i]]++;
        nb_pixel_2[Img2[i]]++;
    }

    for (int i = 0; i < 255; ++i) {
        ddp_1[i] = nb_pixel_1[i] / ((double) nH * nW);
        ddp_2[i] = nb_pixel_2[i] / ((double) nH * nW);
    }

    f_1[0] = ddp_1[0];
    f_2[0] = ddp_2[0];
    for (int i = 1; i < 255; ++i) {
        f_1[i] = f_1[i - 1] + ddp_1[i];
        f_2[i] = f_2[i - 1] + ddp_2[i];
    }

    printf("couleur img-1 img-2\n");
    for (int i = 0; i < 255; ++i) {
        printf("%i %f %f\n", i, f_1[i], f_2[i]);
    }
}

int main(int argc, char* argv[])
{
    char cNomImgLue1[250];
    char cNomImgLue2[250];
    int nH, nW;
    OCTET *Img1;
    OCTET *Img2;

    sscanf(argv[1],"%s",cNomImgLue1);
    sscanf(argv[2],"%s",cNomImgLue2);
    
    lire_nb_lignes_colonnes_image_pgm(cNomImgLue1, &nH, &nW);
    allocation_tableau(Img1, OCTET, nH * nW);
    allocation_tableau(Img2, OCTET, nH * nW);
    lire_image_pgm(cNomImgLue1, Img1, nH * nW);
    lire_image_pgm(cNomImgLue2, Img2, nH * nW);

    repartition(Img1, Img2, nH, nW);
    free(Img1);
    free(Img2);
    return 0;
}
