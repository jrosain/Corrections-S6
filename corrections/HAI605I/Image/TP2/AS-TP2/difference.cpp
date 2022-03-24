    // test_couleur.cpp : Seuille une image en niveau de gris

    #include <stdio.h>
    #include "image_ppm.h"

    int main(int argc, char* argv[])
    {
    char cNomImgLue[250], cNomImgLue2[250], cNomImgEcrite[250];
    int nH, nW, nTaille, nH2, nW2, nTaille2;

    if (argc != 4) 
        {
        printf("Usage: ImageInSeuil.pgm ImageInDilat.pgm ImageOut.pgm\n"); 
        exit (1) ;
        }

    sscanf (argv[1],"%s",cNomImgLue) ;
    sscanf (argv[2],"%s",cNomImgLue2);
    sscanf (argv[3],"%s",cNomImgEcrite);

    OCTET *ImgIn, *ImgOut, *ImgIn2;

    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;

    lire_nb_lignes_colonnes_image_pgm(cNomImgLue2, &nH2, &nW2);
    nTaille2 = nH2 * nW2;

    if (nTaille != nTaille2) {
        printf("Les tailles des images sont différentes ! fdp");
        exit(1);
    }

    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);
    allocation_tableau(ImgOut, OCTET, nTaille);
    allocation_tableau(ImgIn2, OCTET, nTaille);
    lire_image_pgm(cNomImgLue2, ImgIn2, nH * nW);

        // Erosion
        for (int i=0; i < nH; i++) {
            for (int j=0; j < nW; j++) {
                if (ImgIn[(i)*nW+(j)] == ImgIn2[(i)*nW+(j)]) {
                    ImgOut[(i)*nW+(j)] = 255;
                }
                else {
                    ImgOut[(i)*nW+(j)] = 0;
                }
            }
        }


    ecrire_image_pgm(cNomImgEcrite, ImgOut,  nH, nW);
    free(ImgIn); free(ImgOut); free(ImgIn2);

    return 1;
}