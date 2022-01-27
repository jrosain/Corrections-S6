#include "afd.h"

// Pour comprendre les transitions et les états de l'automate voir le TD

void creerAfd() {
    // Initialisation de notre automate
    for (int a = 0; a < NBETAT; a++) {
        for (int c = 0; c < 256; c++) {
            // -1 signifie que l'automate 'a' n'a pas de transition avec le caractère 'c'
            TRANS[a][c] = -1;
        }
        
        // Ce tableau représente les états finaux, de base, aucun état n'est final
        // Si un état est final, il renvoie un jeton
        JETON[a] = NOT_FINAL;			    
    }

    // Transitions entiers et flotants
    classe(EINIT, '1', '9', EENT);
    classe(EINIT, '.', '.', EF);
    classe(EINIT, '0', '0', EZ);
    classe(EENT, '0', '9', EENT);
    classe(EENT, '.', '.', EFLOT);
    classe(EZ, '.', '.', EFLOT);
    classe(EF, '0', '9', EFLOT);
    classe(EFLOT, '0', '9', EFLOT);

    // Transitions if et id
    classe(EINIT, 'a', 'z', EID);
    classe(EINIT, 'A', 'Z', EID);
    classe(EINIT, 'i', 'i', EI);
    classe(EI, 'a', 'z', EID);
    classe(EI, 'A', 'Z', EID);
    classe(EI, '0', '9', EID);
    classe(EI, '_', '_', EID);
    classe(EI, 'f', 'f', EIF);
    classe(EIF, 'a', 'z', EID);
    classe(EIF, 'A', 'Z', EID);
    classe(EIF, '0', '9', EID);
    classe(EIF, '_', '_', EID);
    classe(EID, 'a', 'z', EID);
    classe(EID, 'A', 'Z', EID);
    classe(EID, '0', '9', EID);
    classe(EID, '_', '_', EID);

    // Transitions blancs
    classe(EINIT, '\n', '\n', EB);
    classe(EINIT, '\t', '\t', EB);
    classe(EINIT, '\r', '\r', EB);
    classe(EINIT, ' ', ' ', EB);
    classe(EB, '\n', '\n', EB);
    classe(EB, '\t', '\t', EB);
    classe(EB, '\r', '\r', EB);
    classe(EB, ' ', ' ', EB);

    // Transitions commentaires C++
    classe(EINIT, '/', '/', ES);
    classe(ES, '/', '/', ESS);
    // Ici on dit que tous les caractères ont une transition de ESS vers ESS
    // Juste après on écrase la transition pour le caractère '\n'
    classe(ESS, 0, 255, ESS);
    classe(ESS, '\n', '\n', ECOMCPP);

    // Transitions commentaires C
    classe(ES, '*', '*', ESE);
    classe(ESE, 0, 255, ESE);
    classe(ESE, '*', '*', ESEE);
    classe(ESEE, 0, 255, ESE);
    classe(ESEE, '*', '*', ESEE);
    classe(ESEE, '/', '/', ECOMC);

    // Etats finaux
    JETON[EENT] = LITENT;
    JETON[EZ] = LITENT;
    JETON[EFLOT] = LITFLOT;
    JETON[EI] = ID;
    JETON[EIF] = IF;
    JETON[EID] = ID;
    JETON[EB] = BLANK;
    JETON[ECOMCPP] = COMCPP;
    JETON[ECOMC] = COMC;
}

void classe(int ed, int cd, int cf, int ef) {
    /**
     * En C, les char sont représentés comme des entiers
     * Les caractères alphabétiques se suivent : par exemple A = 65, B = 66, ..., Z = 90
     * Ainsi, cette fonction permet d'éviter de répéter 26 fois la même chose pour les lettres par exemple
    **/
    for (int c = cd; c <= cf; ++c) {
        TRANS[ed][c] = ef;
    }
}