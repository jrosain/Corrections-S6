/* Zone de définition */

%{
    #include "definition.c"
%}

/* Zone des règles */

%%
[a-zA-Z_][a-zA-Z0-9_]*                          { return VARIABLE; }
[0-9]+                                          { return NUMBER; }      // Entiers
([0-9]+\.[0-9]*|\.[0-9]+)([eEdD][+-]?[0-9]+)?f? { return NUMBER; }      // Flottants
(\(|\)|\^|\*|\/|\+|\-)                          { return yytext[0]; }   // Caractère d opérations et parenthèses
\n                                              { return FIN; }
%%

/* Zone des fonctions C */

#define FLEX_VAR

#include "calcdesc.c"

/*

=================================
=====       GRAMMAIRE       =====
=================================

Définissons la gramaire intuitive suivante
(I défini un entier = symbole terminal):

E -> E+E|E*E|(E)|I

Cette grammaire est ambigüe car nous n'avons pas défini de priorité
des opérateurs, soit terme (T) l'élément d'une somme et fecteur (F)
l'élement d'un produit :

E -> E+T|T
T -> T*F|F
F -> (E)|I

Cette grammaire est non ambiguë mais possède de la récusrivité à gauche
Nous pouvons utiliser l'algorithme de suppression de la récursivité à
gauche (Algo 10 ou 11) et nous obtenons

E  -> T.RE
RE -> +T.RE|€
T  -> F.RT
RT -> *F.RT|€
F  -> (E)|I

=================================
=====     ASSOCIATIVITE     =====
=================================

Les fonctions de calculs sont toujours des fonctions récursives (RE et RT).
Comme on lit de gauche à droite, le terme du gauche des opérations et déjà
calculé et est donc fournis à la fonction pour faire le calcul.

En fonction du type d'associativité des opérations, le calcul se fait
différemment.

(a, b et c sont des expressions)

Pour l'associativité à gauche, on calcule notre terme et puis on continue voir
s'il y en a d'autres : a + b + c === (a + b) + c.

Donc si on nous donne un terme, la fonction doit calculer le prochain terme
et appliquer l'opération AVANT de se rappeler

(a + b) + c : lors de l'appel pour le premier +, on nous donne a en paramètre,
je calcule b (T pour le +) et je le somme avant de faire ma récursion
(RE pour le +).

On donne donc a + b en paramètre de RE pour le second +.

=> RE(a + T())

Pour l'associativité à droite, on calcule en premier le terme suivant et on
effectue l'opération après : a + b + c = a + (b + c).

Donc si on nous donne un terme, la fonction doit calculer le prochain terme et
se rappeler sur ce terme AVANT d'effectuer l'opération

a + (b + c) : lors de l'appel pour le premier +, on nous donne a en paramètre,
je calcule b (T pour le +) et j'appelle RE sur mon terme calculer avant de sommer
mon terme et a.

On donne b en paramètre de RE pour le second +.

=> a + RE(T())

=================================
=====   MISE EN PRATIQUE    =====
=================================

1. Les opérations :

On considère * et + comme associatif à gauche (mais on pourrait le faire à
droite !)
On considère - et / comme associatif à gauche
On considère ^ comme associatif à droite

2. La logique :

On considère /\, \/ et <=> comme associatif à gauche
On considère => comme associatif à droite

Grammaire :

E -> A.RE       Expr
RE -> +A.RE|€   Reste Expr
A -> S.RA       Addition
RA -> -S.RA|€   Reste Addition
S -> M.RS       Soustraction
RS -> *M.RS|€   Reste Soustraction
M -> D.RM       Multiplication
RM -> /D.RM|€   Reste Multiplication
D -> P.RD       Division
RD -> ^P.RD|€   Reste Division
P -> (E)|I      Puissance

*/