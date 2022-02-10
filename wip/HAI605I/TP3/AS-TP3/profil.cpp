#include <stdio.h>
#include "image_ppm.h"
using namespace std;

int main(int argc, char* argv[])
{
    char cNomImgLue[250], cNomTxtEcrite[250];
    int nH, nW, nTaille, nb, type;
    int *TxtOut;
        

    if (argc != 5) 
        {
        printf("Usage: ImageIn.pgm file_res.dat col(1) or line(2); nb of line or col\n"); 
        exit (1) ;
        }

    sscanf(argv[1],"%s",cNomImgLue) ;
    sscanf(argv[2],"%s",cNomTxtEcrite);
    sscanf(argv[3],"%d",&type);
    sscanf(argv[4],"%d",&nb);

    OCTET *ImgIn;

    lire_nb_lignes_colonnes_image_pgm(cNomImgLue, &nH, &nW);
    nTaille = nH * nW;
    allocation_tableau(ImgIn, OCTET, nTaille);
    lire_image_pgm(cNomImgLue, ImgIn, nH * nW);

    FILE* file_output;
        if((file_output = fopen(cNomTxtEcrite,"w")) == NULL) {
            exit(EXIT_FAILURE);
    };
    
    if(type == 1) {
        allocation_tableau(TxtOut, int, nH);
        for (int i=0; i < nH; i++) {
            fprintf(file_output, "%d\t%d\n", i, ImgIn[i*nW+nb]);
        }
    }
    else {
        allocation_tableau(TxtOut, int, nW);
        for (int j=0; j < nW; j++) {
            fprintf(file_output, "%d\t%d\n", j, ImgIn[nb*nW+j]);
        }
    }

    fclose(file_output);
    free(ImgIn);

    
    return 1;
}