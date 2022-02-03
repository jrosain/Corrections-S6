
#include <stdio.h>
#include "image_ppm.h"

enum Flags {
    EROSION,                // -e
    DILATATION,             // -d
    OUVERTURE,              // -o
    FERMETURE,              // -f
    FERMOUVETURE,           // -fo
    DIL3ERO6DIL3,           // -tacos12viandes
};

int min(int a, int b) {
    return (a > b) ? b : a;
}
int max(int a, int b) {
    return (a < b) ? b : a;
}

// fait au choix une erosion ou une dilatation
void transformation(OCTET* ImgIn, OCTET* ImgOut, int nH, int nW, bool erosion, bool couleur) {
    int step = 1;
    if (couleur) {
        step = 3;
        nW *= 3;
    }
    // pour chaque pixel
    for (int i=0; i < nH; i++) { 
        for (int j=0; j < nW; j+=step) {
            int p1 = 255;
            int p2 = 255;
            int p3 = 255;
            // valeur qui sera assignée
            if (erosion) {
                p1 = 0;
                if (couleur) {
                    p2 = 0;
                    p3 = 0;
                }
            }
            // pour les 8 pixels autour
            for(int a=-1; a<2; a++) {
                for(int b=-1; b<2; b++){
                    if (a!=0 || b!=0) { //on ne regarde pas le pixel central
                        if (couleur) {
                            if(i+a >=0 && i+a < nH && j+3*b >=0 && j+3*b < nW) { //on ne dépasse pas des bords
                                if (erosion) {
                                    p1 = max(p1, ImgIn[(i+a)*nW +j+3*b]);
                                    p2 = max(p2, ImgIn[(i+a)*nW +j+1+3*b]);
                                    p3 = max(p3, ImgIn[(i+a)*nW +j+2+3*b]);
                                } else {
                                    p1 = min(p1, ImgIn[(i+a)*nW +j+3*b]);
                                    p2 = min(p2, ImgIn[(i+a)*nW +j+1+3*b]);
                                    p3 = min(p3, ImgIn[(i+a)*nW +j+2+3*b]);
                                }
                            }
                        } else {
                            if(i+a >=0 && i+a < nH && j+b >=0 && j+b < nW) {
                                if (erosion) {
                                    p1 = max(p1, ImgIn[(i+a)*nW +j+b]);
                                } else {
                                    p1 = min(p1, ImgIn[(i+a)*nW +j+b]);
                                }
                            }
                        }
                    } 
                } 
            }
            if (couleur) {
                ImgOut[i*nW+j] = p1; 
                ImgOut[i*nW+j+1] = p2;
                ImgOut[i*nW+j+2] = p3;
            } else {
                ImgOut[i*nW+j] = p1; 
            }
        }
    } 
}

int main(int argc, char* argv[])
{
    char cNomImgLue[250], cNomImgEcrite[250], f[10], c[10];
    int nH, nW, nTaille, flag;
    bool couleur;
    
    // arguments
    if (argc < 4) {
        printf("Usage: [FlagType] [FlagCouleur] ImageIn.pgm ImageOut.pgm\n"); 
        exit (1) ;
    }
    // activer le bon flag
    sscanf (argv[1],"%s",f);
    if (f[1] == 'e') {
        flag = EROSION;
    } else if (f[1] == 'd' && strlen(f) < 3) {
        flag = DILATATION;
    } else if (f[1] == 'o') {
        flag = OUVERTURE;
    } else if (f[1] == 'f' && strlen(f) < 3) {
        flag = FERMETURE;
    } else if (f[1] == 'f' && f[2] == 'o') {
        flag = FERMOUVETURE;
    } else {
        flag = DIL3ERO6DIL3;
    }
    // couleur ou noir et blanc
    sscanf (argv[2],"%s",c);
    couleur = (c[1] == 'c');  
    // emplacement des images
    sscanf (argv[3],"%s",cNomImgLue) ;
    sscanf (argv[4],"%s",cNomImgEcrite);

    //déclarer les tableaux
    OCTET *ImgIn, *ImgOut, *ImgInter; 
    //lire les images
    if (couleur) {
        lire_nb_lignes_colonnes_image_ppm(cNomImgLue, &nH, &nW);
    } else {
        lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    } 
    nTaille = nH * nW;
    if(couleur) {
        nTaille *= 3;
    }
    //allouer l'espace des tableaux
    allocation_tableau(ImgIn, OCTET, nTaille);
    allocation_tableau(ImgInter, OCTET, nTaille);
    allocation_tableau(ImgOut, OCTET, nTaille);
    if (couleur) {
        lire_image_ppm(cNomImgLue, ImgIn, nH * nW);
    } else {
        lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    }

    //action
    switch(flag) {
        case EROSION:
            transformation(ImgIn, ImgOut, nH, nW, true, couleur);
            break;
        case DILATATION:
            transformation(ImgIn, ImgOut, nH, nW, false, couleur);
            break;
        case OUVERTURE:
            transformation(ImgIn, ImgInter, nH, nW, true, couleur);
            transformation(ImgInter, ImgOut, nH, nW, false, couleur);
            break;
        case FERMETURE:
            transformation(ImgIn, ImgInter, nH, nW, false, couleur);
            transformation(ImgInter, ImgOut, nH, nW, true, couleur);
            break;
        case FERMOUVETURE:
            transformation(ImgIn, ImgInter, nH, nW, false, couleur);
            transformation(ImgInter, ImgOut, nH, nW, true, couleur);
            transformation(ImgOut, ImgInter, nH, nW, true, couleur);
            transformation(ImgInter, ImgOut, nH, nW, false, couleur);
            break;
        case DIL3ERO6DIL3:
            //3 dilatations
            transformation(ImgIn, ImgInter, nH, nW, false, couleur);
            transformation(ImgInter, ImgOut, nH, nW, false, couleur);
            transformation(ImgOut, ImgInter, nH, nW, false, couleur);
            //6 erosions
            transformation(ImgInter, ImgOut, nH, nW, true, couleur);
            transformation(ImgOut, ImgInter, nH, nW, true, couleur);
            transformation(ImgInter, ImgOut, nH, nW, true, couleur);
            transformation(ImgOut, ImgInter, nH, nW, true, couleur);
            transformation(ImgInter, ImgOut, nH, nW, true, couleur);
            transformation(ImgOut, ImgInter, nH, nW, true, couleur);
            //3 dilatations
            transformation(ImgInter, ImgOut, nH, nW, false, couleur);
            transformation(ImgOut, ImgInter, nH, nW, false, couleur);
            transformation(ImgInter, ImgOut, nH, nW, false, couleur);
            break;
        default:
            break;
    }

    if (couleur) {
        ecrire_image_ppm(cNomImgEcrite, ImgOut,  nH, nW);
    } else {
        ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    }
    free(ImgIn); free(ImgInter); free(ImgOut); 

    return 1;
}
