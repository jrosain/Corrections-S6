/**
 * fichier: arbin.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
#include <stdlib.h>
#include <stdio.h>

#include "arbin.h"

/*----------------------GREFFERGAUCHE-----------------------------------------*/
void ab_greffergauche(Arbin pere, Arbin filsg) {
    ab_vider(&ab_sag(pere));		/* vider l'ancien sag */
    pere->fg=filsg;		/* le remplacer */
}

/*----------------------GREFFERDROITE-----------------------------------------*/
void ab_grefferdroite(Arbin pere, Arbin filsd){
    ab_vider(&ab_sad(pere));
    pere->fd=filsd;
}

/*----------------------CONSTRUIRE--------------------------------------------*/
Arbin ab_construire(int rac, Arbin g, Arbin d){
    Arbin nouv = (Arbin) malloc(sizeof(Noeudbin)) ;
    nouv->val=rac;
    nouv->fg=g;
    nouv->fd=d;
    return(nouv) ;
}

/*----------------------COPIERA-----------------------------------------------*/
Arbin ab_copier(Arbin a){
    Arbin nouv;			/* nouvel arbin copie */
    if (ab_vide(a)) return NULL;	/* arbin vide */
    nouv = (Arbin) malloc(sizeof(Noeudbin)) ;
    nouv->val=a->val;
    nouv->fg=ab_copier(ab_sag(a));
    nouv->fd=ab_copier(ab_sad(a));
    return(nouv) ;
} 

/*----------------------VIDERA------------------------------------------------*/
void ab_vider(Arbin *pa){	
    Arbin *pg,*pd;			/* arbins de sauvegarde */
    if (ab_vide(*pa)) return;		/* arbin vide */
    pg=&(ab_sag(*pa));			/* possible car sag() est une macro */
    pd=&(ab_sad(*pa));
    ab_vider(pg);
    ab_vider(pd);
    free(*pa);			/* on est sur une feuille */
    *pa=NULL;			/* mettre le pointeur a NULL  */
    return;
} 
/*----------------------AFFICHERAR-fonction privée (static) ------------------*/
static void ab_afficherR(Arbin a,int indent){
    int i;
    for (i=0;i<indent;i++)
        printf("    ");		/* 4 espaces par profondeur d'indentation */
    if (ab_vide(a))
        printf("\r");
    else {
        printf("%c\n",ab_racine(a));
        ab_afficherR(ab_sag(a),indent+1);
        ab_afficherR(ab_sad(a),indent+1);
  }
}
/*----------------------AFFICHERA---------------------------------------------*/
void ab_afficher(Arbin a){
    ab_afficherR(a,0);
}
