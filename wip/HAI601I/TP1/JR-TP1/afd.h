/**
 * @file afd.h     
 * @author Johann Rosain
 * @brief Définition d'un AFD
 */
#define INVALID_TRANS -1

/* Énumération des différents états possibles de l'AFD défini par a(b+c)|bd. */
enum Etat {
    EINIT,
    EI,
    EIF,
    EID,
    EENT,
    E2,
    EFLOT,
    EP,
    EB,
    ES,
    ESS,
    ECOMCPP,
    ESE,
    ESSE,
    ECOMC,
    NBETAT,
};
/* Énumération des états finaux. */
enum FinalState {
    ID = 1,
    IF,
    LITENT,
    LITFLOT,
    EMPTY = -1,
    COMCPP = -2,
    COMC = -3,
};
/* Construction de l'AFD avec les règles données par l'utilisateur. */
void creerAfd();

/** Construit un ensemble de transitions de ed à ef pour un intervale de char
  * @param ed l'état de départ
  * @param ef l'état final
  * @param cd char de début
  * @param cf char de fin
 **/
void classe(int ed, int cd, int cf, int ef);

/* Table de transition -> état suivant (INVALID_TRANS si non défini) */
int TRANS[NBETAT][256];
/* Jeton à retourner. FINAL_STATE si c'est un état final. */	
int JETON[NBETAT];		