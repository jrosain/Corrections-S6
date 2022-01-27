/**
 * @file analex.h
 * @author Benoît Huftier
 * @brief Définition de la fonction analex() qui retourne un entier positif si OK, 
 * 0 si fin de fichier. Le filtrage est permis gâce aux jetons négatifs.
**/
 
#include <string.h>

// Variable qui contient le dernier lexeme calculé avec la fonction analex()
char lexeme[1024];

/** 
 * Lit dans l'entrée standard le mot le plus long se terminant en un état final 
 * de l'automate défini par TRANS, puis retourne le JETON correspondant.
 * @returns le JETON entier correspondant à l'état final de l'AFD
 */
int analex();