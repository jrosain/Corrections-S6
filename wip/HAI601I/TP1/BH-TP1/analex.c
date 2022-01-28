#include <stdio.h>

#include "analex.h"
#include "afd.h"

/**
 * Cette fonction renvoie la première chaine de caractères qui correspond à un jeton
 * de l'automate défini dans afd.h.
 * 
 * Pour ce faire elle lit les caractères de l'entrée standard un à un et vérifie les
 * transitions dans l'automate.
 * La fonction getchar() permet de lire ce caractère et d'avancer le "pointeur" dans
 * le fichier.
 *
 * Lorsqu'on se trouve dans un état dont la lettre ne possède aucune transition vers
 * un autre état ou qu'il n'y a plus de lettre, on s'arrête.
 *
 * Au moment où l'on s'arrête, nous avons pris un caractère de trop (logique, sinon
 * comment vérifier que ce caractère n'appartient pas aux transitions de l'état
 * actuel ?). Il faut donc le remettre dans l'entrée standard, ce qui est fait grâce
 * à la fonction ungetc(c, stdin). stdin étant une constante pour représenter le
 * descripteur de fichier de l'entrée standard.
 *
 * À partir de ce moment, pour récupérer notre lexeme (chaine de caractères matchant 
 * un chemin qui se termine par un état final de l'automate), plusieurs possibilités
 * peuvent survenir.
 *
 * A. On a chopé un état final sur le chemin
 *    - On retourne au dernier état trouvé et on récupère la chaîne qui s'était
 *      formée à ce moment.
 *    - On n'oublie pas de replacer tous les caractères non utilisés dans l'entrée
 *      standard !
 *
 * B. Cas spécifique à notre programme pour qu'il s'arrête : l'entrée est vide
 *    - Si l'entrée est vide, on renvoie 0, ce qui nous permet d'arrêter la boucle
 *      du main.
 *
 * C. Aucun état final n'a été trouvé
 *    - Aucun jeton n'a pu être fabriqué, on considère uniquement le premier caractère
 *      comme résultat.
 *    - On considère la valeur du jeton comme étant la valeur ascii du caractère.
 *    - Encore une fois on remet tous les caractères non utilisés dans l'entrée
 *      standard pour pouvoir les reparcourir au prochain appel ! Comme on ne renvoie
 *      qu'un seul caractère, il faut donc en remettre n - 1 (n étant le nombre de
 *      caractères récupérés)
 *
 * A et C ont été découpé en deux parties dans le programme pour plus de compréhension.
 *  - Les cas particuliers où seul le dernier caractère doit être remis.
 *  - Les cas un peu plus complexes avec une boucle for.
**/
int analex() {
    // On remet le lexeme sur une chaine vide, c'est comme si l'ancien est "supprimé"
    lexeme[0] = '\0';

    // Etat actuel du parcours de l'automate, on commence au seul état initial
    int etat = EINIT;
    int efinal = -1;		/* pas d'état final déjà vu */
    int lfinal = 0;			/* longueur du lexème final */

    // Caractère actuellement observé par l'automate
    int c;

    // Tant que nous avons une transition dans l'automate de l'état actuel avec le caractère c
    while ((c = getchar()) != EOF && TRANS[etat][c] != -1) {
        strncat(lexeme, (char*)&c, 1);

        // printf("%i ---> %c ---> %i ", etat, c, TRANS[etat][c]);
        
        // Notre nouvel état, c'est celui défini par la transition
        etat = TRANS[etat][c];
        
        // On se souvient de l'état si c'est un état final
        // Ainsi, on pourra revenir en arrière sur le dernier état final
        if (JETON[etat]) {
            efinal = etat;
            lfinal = strlen(lexeme);
        }
    }

    // Cas A "facile" : l'état actuel en sortant de la boucle est un état final
    if (JETON[etat]) {
        // On a pris un caractère de trop avec le getchar() donc on le remet
        ungetc(c, stdin);

        // On ne veut pas renvoyer les Jeton de types "commentaires" etc...
        // (ils ont été définis comme négatif, voir afd.h)
        return (JETON[etat] < 0 ? analex() : JETON[etat]);
    }
    // Cas A "boucle for" : si on a déjà choppé un état final mais que ce n'est pas le dernier
    else if (efinal > -1) {
        ungetc(c, stdin);

        // On remet tous les caractères pris en trop
        for(int i = strlen(lexeme) - 1; i >= lfinal; i--)
            ungetc(lexeme[i], stdin);

        // On définit la fin de notre chaine au bon endroit
        lexeme[lfinal] = '\0';

        return (JETON[efinal] < 0 ? analex() : JETON[efinal]);
    }
    // Cas B, l'utilisateur à écrit CTRL-D, on veut sortir du programme
    else if (strlen(lexeme) == 0 && c == EOF) {
        return 0;
    }
    // Cas C "facile" : le premier caractère ne matchait rien, on le renvoie seul
    else if (strlen(lexeme) == 0) {
        lexeme[0] = c;
        lexeme[1] = '\0';
        return c;
    }
    // Cas C "boucle for" : plusieurs caractères ne matchaient rien, on ne renvoie que le premier
    else {
        ungetc(c, stdin);
        for(int i = strlen(lexeme) - 1; i >= 1; i--)
            ungetc(lexeme[i], stdin);

        lexeme[1] = '\0';
        return lexeme[0];
    }
}
