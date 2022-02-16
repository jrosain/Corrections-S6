#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void histogramme(OCTET* ImgIn, int nH, int nW) {
    int nb_pixel[255];

    for (int i = 0; i < 255; ++i) {
        nb_pixel[i] = 0;
    }

    for (int i = 0; i < nH * nW; ++i) {
        nb_pixel[ImgIn[i]]++;
    }

    for (int i = 0; i < 255; ++i) {
        printf("%i %i\n", i, nb_pixel[i]);
    }
}

void histogramme_couleur(OCTET* ImgIn, int nH, int nW) {
    int nb_red[255];
    int nb_green[255];
    int nb_blue[255];

    for (int i = 0; i < 255; ++i) {
        nb_red[i] = nb_green[i] = nb_blue[i] = 0;
    }

    for (int i = 0; i < nH * nW; ++i) {
        nb_red[ImgIn[3*i]]++;
        nb_green[ImgIn[3*i + 1]]++;
        nb_blue[ImgIn[3*i + 2]]++;
    }

    // plot for [col=2:4] "histo.dat" using col with lines title columnheader
    printf("nb rouge vert bleu\n");
    for (int i = 0; i < 255; ++i) {
        printf("%i %i %i %i\n", i, nb_red[i], nb_blue[i], nb_green[i]);
    }
}

void profil_line(OCTET* ImgIn, int nH, int nW, int line) {
    for (int i = 0; i < nW; ++i) {
        printf("%i %i\n", i, ImgIn[line * nW + i]);
    }
}

void inverse(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW) {
    for (int i = 0; i < nH * nW; ++i) {
        ImgOut[i] = -ImgIn[i] + 255;
    }
}

void filtre_flou1(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW) {
    for (int i = 0; i < nW; ++i) {
        for (int j = 0; j < nH; ++j) {
            int val = ImgIn[j * nW + i];
            if (j != 0 && i != 0 && j != nH - 1 && i != nW - 1) {
                val += ImgIn[(j + 1) * nW + i];
                val += ImgIn[(j - 1) * nW + i];
                val += ImgIn[j * nW + i + 1];
                val += ImgIn[j * nW + i - 1];
                val /= 5;
            }
            ImgOut[j * nW + i] = val;
        }
    }
}

void filtre_flou2(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    int facteur = color ? 3 : 1;
    int boucle = color ? 3 : 1;

    for (int i = 0; i < nW; ++i) {
        for (int j = 0; j < nH; ++j) {
            for (int k = 0; k < boucle; k++) {
                int val = 0;
                int nb = 0;

                for (int x = max(0, i - 1); x <= min(i + 1, nW - 1); ++x) {
                    for (int y = max(0, j - 1); y <= min(j + 1, nH - 1); ++y) {
                        val += ImgIn[facteur*(y * nW + x) + k];
                        nb++;
                    }
                }

                ImgOut[facteur*(j * nW + i) + k] = val / nb;
            }
        }
    }
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250];
    char cNomImgEcrite[250];
    int nH, nW, nTaille;
    
    if (argc < 3) {
        printf("Usage: ImageIn.p(g|p)m Exo [params selon exo]\n"); 
        exit(1);
    }

    int exo = atoi(argv[2]);

    if (exo <= 0 || exo > 5) {
        printf("Exo %i inconnu\n", exo);
        printf("1: histogramme, 2: profil de ligne, 3: inverse, 4 filtre flou 1, 5 filtre flou 2\n");
        exit(1);
    }

    bool needWriteOutImage = exo != 1 && exo != 2;

    if (needWriteOutImage) {
        if (argc < 4) {
            printf("L'exo %i demande une image de sortie pour fonctionner\n", exo);
            exit(1);
        }
        sscanf(argv[3],"%s",cNomImgEcrite);
    }

    sscanf(argv[1],"%s",cNomImgLue);

    char ext[4] = "ppm";
    bool color = strcmp(cNomImgLue + strlen(cNomImgLue) - 3, ext) == 0;
    
    if (color)  lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
    else        lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);

    nTaille = color ? nH * nW * 3 : nH * nW;
    
    OCTET *ImgIn, *ImgOut;
    allocation_tableau(ImgIn, OCTET, nTaille);

    if (needWriteOutImage) {
        allocation_tableau(ImgOut, OCTET, nTaille);
    }

    if (color)  lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    else        lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    
    switch (exo) {
        case 1:
            if (color)
                histogramme_couleur(ImgIn, nH, nW);
            else
                histogramme(ImgIn, nH, nW);
            break;
        case 2:
            if (argc < 4) {
                printf("Il manque le numéro de la ligne en 3ème paramètre\n");
                break;
            }
            profil_line(ImgIn, nH, nW, atoi(argv[3]));
            break;
        case 3:
            inverse(ImgIn, ImgOut, nH, nW);
            break;
        case 4:
            filtre_flou1(ImgIn, ImgOut, nH, nW);
            break;
        case 5:
            filtre_flou2(ImgIn, ImgOut, nH, nW, color);
            break;
    }

    if (needWriteOutImage) {
        if (color)  ecrire_image_ppm(cNomImgEcrite, ImgOut, nH, nW);
        else        ecrire_image_pgm(cNomImgEcrite, ImgOut, nH, nW);

        free(ImgOut);
    }

    free(ImgIn);

    return 1;
}
