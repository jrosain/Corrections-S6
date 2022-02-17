/** @file arbin.h 
 * @brief en-tête définissant les structures, types, fonctions sur les arbres 
 * binaires d'entiers.
 * @author Meynard Michel
*/
#ifndef _ARBINH
#define _ARBINH

#ifndef NULL
#define NULL 0
#endif 

/*----------------------- Types Unions Structures ---------------------------*/
/** type pointeur sur la racine de l'arbre binaire d'entiers */
typedef struct Noeudbin * Arbin; 

/** type noeud d'un arbre binaire d'entiers */
typedef struct Noeudbin {
    int val ;
    Arbin fg;
    Arbin fd ;
} Noeudbin ;
/*---------------------------FONCTIONS----------------------------------------*/

/** macro fonction créant un Arbin vide (retourne pointeur nul) */
#define ab_creer() (NULL)	

/** macro fonction retournant le sous-arbre gauche d'un Arbin
 *@param a un Arbin
 *@return le sous-arbre gauche de a 
*/
#define ab_sag(a) ((a)->fg)	

/** macro fonction retournant le sous-arbre droit d'un Arbin
 *@param a un Arbin
 *@return le sous-arbre droit de a 
*/
#define ab_sad(a) ((a)->fd)	/* retourne le sous-arbre droit de a */

/** macro fonction  testant si un Arbin est vide 
 *@param  a un Arbin
 *@return vrai si a est vide, faux sinon
*/
#define ab_vide(a) (a==NULL)

/** macro fonction retournant la racine d'un Arbin
 *@param a un Arbin
 *@return l'entier situé à la racine
*/
#define ab_racine(a) ((a)->val)

/** @remark Ces 5 pseudo-fonctions (macros) sont definies quel 
 * que soit le type de l'Arbin (entier, car, arbre,...) 
*/

/** fonction remplaçant le sag(pere) par filsg et vidant l'ancien sag. Attention,
 * opération MODIFIANTE !
 *@param pere un Arbin
 *@param filsg l'Arbin qu'il faut greffer à la place du sag actuel de pere
 */
void ab_greffergauche(Arbin pere, Arbin filsg); 

/** fonction remplaçant le sad(pere) par filsd et vidant l'ancien sag. Attention,
 * opération MODIFIANTE !
 *@param pere un Arbin
 *@param filsd l'Arbin qu'il faut greffer à la place du sad actuel de pere
 */
void ab_grefferdroite(Arbin pere, Arbin filsd); 

/** fonction construisant un nouvel Arbin à partir d'une valeur entière qui 
 * deviendra la racine et de deux sous arbres.
 *@param rac l'entier racine
 *@param g un Arbin qui devient sag
 *@param d un Arbin qui devient sad
 *@return l'Arbin construit
 */
Arbin ab_construire(int rac, Arbin g, Arbin d);


/** fonction copiant (clone) la structure d'un Arbin
 *@param a un Arbin
 *@return l'Arbin copié 
 */
Arbin ab_copier(Arbin a);

/** fonction vidant un Arbin (désallocation). Attention, opération MODIFIANTE !
 *@param pa un pointeur sur Arbin
 */
void ab_vider(Arbin * pa);

/** fonction affichant un Arbin de manière indentée. Attention, racine(a) est 
 * affichée comme un char
 *@param a l'Arbin à afficher
 */
void ab_afficher(Arbin a);


#endif /* _ARBINH */
