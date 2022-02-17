#include <cmath>
#include <stdio.h>
#include <algorithm>
#include "image_ppm.h"

using namespace std;

void seuillage(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, int seuil, bool color) {
    for (int i = 0; i < nH * nW * (color ? 3 : 1); ++i) {
        ImgOut[i] = ImgIn[i] > seuil ? 255 : 0;
    }
}

void profil_line(OCTET* ImgIn, int nH, int nW, int line, bool color) {
    int boucle = color ? 3 : 1;
    for (int i = 0; i < nW; ++i) {
        printf("%i", i);
        for (int j = 0; j < boucle; ++j) {
            printf(" %i", ImgIn[boucle*(line * nW + i) + j]);
        }
        printf("\n");
    }
}

void gradient(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    int facteur = color ? 3 : 1;
    int boucle = color ? 3 : 1;

    for (int i = 0; i < nW - 1; ++i) {
        for (int j = 0; j < nH - 1; ++j) {
            for (int k = 0; k < boucle; k++) {
                int actual = ImgIn[facteur*(j * nW + i) + k];
                int right = ImgIn[facteur*(j * nW + i + 1) + k];
                int bottom = ImgIn[facteur*((j + 1) * nW + i) + k];
                
                int g_vertical = right - actual;
                int g_horizontal = bottom - actual;
                int g = sqrt(pow(g_vertical, 2) + pow(g_horizontal, 2));

                ImgOut[facteur*(j * nW + i) + k] = g;
            }
        }
    }
}

void hysteresis(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, int SB, int SH, bool color) {
    int facteur = color ? 3 : 1;
    int boucle = color ? 3 : 1;

    for (int i = 0; i < nW; ++i) {
        for (int j = 0; j < nH; ++j) {
            for (int k = 0; k < boucle; k++) {
                int val = 0;
                int pix = ImgIn[facteur*(j * nW + i) + k];

                if (pix >= SH) {
                    val = 255;
                }
                else if (pix > SB) {
                    for (int x = max(0, i - 1); x <= min(i + 1, nW - 1); ++x) {
                        for (int y = max(0, j - 1); y <= min(j + 1, nH - 1); ++y) {
                            if (ImgIn[facteur*(y * nW + x) + k] >= SH) {
                                val = 255;
                            }
                        }
                    }
                }

                ImgOut[facteur*(j * nW + i) + k] = val;
            }
        }
    }
}

void filtre(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, int noyau[3][3], bool color) {
    int facteur = color ? 3 : 1;
    int boucle = color ? 3 : 1;

    for (int i = 0; i < nW; ++i) {
        for (int j = 0; j < nH; ++j) {
            for (int k = 0; k < boucle; k++) {
                int val = 0;
                int nb = 0;

                for (int x = max(0, i - 1); x <= min(i + 1, nW - 1); ++x) {
                    for (int y = max(0, j - 1); y <= min(j + 1, nH - 1); ++y) {
                        int f = noyau[x - i + 1][y - j + 1];
                        val += f * ImgIn[facteur*(y * nW + x) + k];
                        nb += f;
                    }
                }

                ImgOut[facteur*(j * nW + i) + k] = val / nb;
            }
        }
    }
}

void moyenneur(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    int noyau[3][3] = {
        {1, 1, 1},
        {1, 1, 1},
        {1, 1, 1}
    };

    filtre(ImgIn, ImgOut, nH, nW, noyau, color);
}

void gaussien(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool color) {
    int noyau[3][3] = {
        {1, 2, 1},
        {2, 4, 2},
        {1, 2, 1}
    };

    filtre(ImgIn, ImgOut, nH, nW, noyau, color);
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

    if (exo <= 0 || exo > 6) {
        printf("Exo %i inconnu\n", exo);
        printf("1: Seuillage, 2: Profil ligne, 3: Norme gradient, 4: Hysteresis, 5: Moyenneur, 6: Gaussien\n");
        exit(1);
    }

    bool needWriteOutImage = exo != 2;

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
            if (argc < 5) {
                printf("Il manque le numéro de seuil en 4ème paramètre\n");
                break;
            }
            seuillage(ImgIn, ImgOut, nH, nW, atoi(argv[4]), color);
            break;
        case 2:
            if (argc < 4) {
                printf("Il manque le numéro de la ligne en 3ème paramètre\n");
                break;
            }
            profil_line(ImgIn, nH, nW, atoi(argv[3]), color);
            break;
        case 3:
            gradient(ImgIn, ImgOut, nH, nW, color);
            break;
        case 4:
            if (argc < 6) {
                printf("Il manque les seuils haut et bas en 4ème et 5ème paramètre\n");
                break;
            }
            hysteresis(ImgIn, ImgOut, nH, nW, atoi(argv[4]), atoi(argv[5]), color);
            break;
        case 5:
            moyenneur(ImgIn, ImgOut, nH, nW, color);
            break;
        case 6:
            gaussien(ImgIn, ImgOut, nH, nW, color);
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
