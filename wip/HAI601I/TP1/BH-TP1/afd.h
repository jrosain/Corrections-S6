/**
 * @file afd.h     
 * @author Benoît Huftier
 * @brief Définition d'un AFD
**/

/**
 * Les énumérations en C sont plutôt utiles pour représenter des valeurs sans se tromper
 * (plus facile de se tromper en utilisant des entiers codés en dur par exemple).
 * Ce sont des constantes qui sont définies de 0 à n si aucune valeur ne leur est fournie.
 * J'ai utilisé cette notation car je la trouve moins difficile à écrire et tout aussi simple à comprendre que les #define du prof
**/
enum Etat {
    EINIT, // <=> 0
    EENT,  // <=> 1
    EZ,    // <=> 2
    EF,    // ...
    EFLOT,
    EI,
    EIF,
    EID,
    EB,
    ES,
    ESS,
    ESE,
    ESEE,
    ECOMC,
    ECOMCPP,
    NBETAT   // Comme les énumérations s'incrémentent de 1 en 1 et commencent à 0, le dernier élément peut être utilisé pour compter le nombre d'éléments de l'énumération, c'est ce qu'on fait ici.
};

/**
 * Ici on donne le numéro des jetons au lieu de laisser le programme décider.
 * En effet, un nombre négatif sera considéré comme un jeton "à jeter" (commentaires, etc...)
 * alors que les jetons positifs seront gardés.
**/
enum TypeJeton {
    COMCPP = -3,
    COMC = -2,
    BLANK = -1,

    NOT_FINAL = 0, // L'état n'est pas un état final

    LITENT = 1,
    LITFLOT = 2,
    IF = 3,
    ID = 4,
};

// Table de transitions : un etat et un caractère renvoie vers un état ou -1 si cette transition n'existe pas dans l'automate
int TRANS[NBETAT][256];
// Etats finaux et valeurs des jetons renvoyés par les états
int JETON[NBETAT];

// Construit l'automate du TD
// Les variables utiles sont stockées dans TRANS et JETON
void creerAfd();

/**
 * Construit un ensemble de transitions de ed à ef pour un intervale de char
 * @param ed l'état de départ
 * @param ef l'état final
 * @param cd char de début
 * @param cf char de fin
**/
void classe(int ed, int cd, int cf, int ef);