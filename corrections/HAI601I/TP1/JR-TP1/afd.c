/**
 * fichier: afd.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
/**
 * @file analex.c  
 * @author Johann Rosain
 * @brief Instancie et crée l'AFD reconnu par l'analex.
 */
#include "afd.h"

void creerAfd() { 
    // Initialisation des tableaux d'état / de transition.
    for (int i = 0; i < NBETAT; i++) {
        for(int j = 0; j < 256; j++) 
            TRANS[i][j] = INVALID_TRANS;    // Initialisation de la transition dans un état invalide.
        JETON[i] = 0;			            // Nombre de jetons trouvé = 0
    }
    // Transitions de l'AFD

    // 1 - ID + IF
    classe(EINIT, 'a', 'z', EID);
    classe(EINIT, 'A', 'Z', EID);
    TRANS[EINIT]['_'] = EID;
    TRANS[EINIT]['i'] = EI;
    TRANS[EI]['f'] = EIF;
    classe(EIF, 'a', 'z', EID);
    classe(EIF, 'A', 'Z', EID);
    TRANS[EIF]['_'] = EID;
    classe(EID, 'a', 'z', EID);
    classe(EID, 'A', 'Z', EID);
    classe(EID, '0', '9', EID);
    TRANS[EID]['_'] = EID;

    // États finaux
    JETON[EI] = JETON[EID] = ID;
    JETON[EIF] = IF;


    // 2 - Décimaux + flottants
    classe(EINIT, '1', '9', EENT);
    classe(EENT, '0', '9', EENT);
    TRANS[EENT]['.'] = EFLOT;
    classe(EFLOT, '0', '9', EFLOT);
    TRANS[EINIT]['0'] = E2;
    TRANS[E2]['.'] = EFLOT;
    TRANS[EINIT]['.'] = EP;
    classe(EP, '0', '9', EFLOT);

    // États finaux
    JETON[EENT] = LITENT;
    JETON[EFLOT] = LITFLOT;
    JETON[E2] = LITENT;


    // 3 - Les caractères vides et les commentaires
    TRANS[EINIT]['/'] = ES;
    TRANS[EINIT]['\n'] = TRANS[EINIT]['\t'] = TRANS[EINIT][' '] = EB;
    TRANS[EB]['\n'] = TRANS[EB]['\t'] = TRANS[EB][' '] = EB;
    TRANS[ES]['/'] = ESS;
    // Tous les caractères ASCII
    classe(ESS, 0, 255, ESS);
    TRANS[ESS]['\n'] = ECOMCPP;
    TRANS[ES]['*'] = ESE;
    classe(ESE, 0, 255, ESE);
    TRANS[ESE]['*'] = ESSE;
    classe(ESSE, 0, 255, ESE);
    TRANS[ESSE]['/'] = ECOMC;
    TRANS[ESSE]['*'] = ESSE;

    // États finaux
    JETON[EB] = EMPTY;
    JETON[ECOMCPP] = COMCPP;
    JETON[ECOMC] = COMC;
}

void classe(int ed, int cd, int cf, int ef) {
    for (int i = cd; i <= cf; ++i) {
        TRANS[ed][i] = ef;
    }
}