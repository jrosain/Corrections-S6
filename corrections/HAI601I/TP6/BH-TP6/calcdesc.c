#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>

#ifndef FLEX_VAR
#include "definition.c"
int yylex();
char* yytext;
#endif

/* les macros sont des blocs : pas de ';' apres */
#define AVANCER {jeton=yylex();numjeton++;}
#define TEST_AVANCE(prevu) {if (jeton==(prevu)) AVANCER else ERREUR_SYNTAXE}
#define ERREUR_SYNTAXE {printf("\nMot non reconnu : erreur de syntaxe \
au jeton numéro %d : %i\n",numjeton,jeton); exit(1);} 

float E(void);
float RE(float);
float A(void);
float RA(float);
float S(void);
float RS(float);
float M(void);
float RM(float);
float D(void);
float RD(float);
float P(void);

int jeton;                      /* jeton courant du flot d'entrée */
int numjeton = 0;               /* numero du jeton courant */

float operation_rule(float(*calc_terme_func)(void), float(*reste_func)(float)) {
    return reste_func(calc_terme_func());
}

float left_associativity(float left_value, int j, float(*op)(float, float), float(*calc_terme_func)(void)) {
    if (jeton == j) {
        AVANCER
        return left_associativity(op(left_value, calc_terme_func()), j, op, calc_terme_func);
    }
    return left_value;
}

float right_associativity(float left_value, int j, float(*op)(float, float), float(*calc_terme_func)(void)) {
    if (jeton == j) {
        AVANCER
        return op(left_value, right_associativity(calc_terme_func(), j, op, calc_terme_func));
    }
    return left_value;
}

float op_plus(float a, float b) { return a + b; }
float op_sous(float a, float b) { return a - b; }
float op_mult(float a, float b) { return a * b; }
float op_div(float a, float b) { return a / b; }
float op_pow(float a, float b) { return pow(a, b); }

/* règle : E -> A.RE     */ float E(void)       { return operation_rule(A, RE); }
/* règle : A -> S.RA     */ float A(void)       { return operation_rule(S, RA); }
/* règle : S -> M.RS     */ float S(void)       { return operation_rule(M, RS); }
/* règle : M -> D.RM     */ float M(void)       { return operation_rule(D, RM); }
/* règle : D -> P.RD     */ float D(void)       { return operation_rule(P, RD); }
/* règle : RE -> +A.RE|€ */ float RE(float g)   { return  left_associativity(g, '+', op_plus, A); }
/* règle : RA -> -S.RA|€ */ float RA(float g)   { return  left_associativity(g, '-', op_sous, S); }
/* règle : RS -> *M.RS|€ */ float RS(float g)   { return  left_associativity(g, '*', op_mult, M); }
/* règle : RM -> /D.RM|€ */ float RM(float g)   { return  left_associativity(g, '/', op_div,  D); }
/* règle : RD -> ^P.RD|€ */ float RD(float g)   { return right_associativity(g, '^', op_pow,  P); }

/* règle : P -> (E)|I    */
float P(void){
    /* regle : P -> (E) */
    if (jeton == '(') {
        AVANCER
        float val = E();
        TEST_AVANCE(')')
        return val;
    }
    /* regle : P -> I */
    else if (jeton == NUMBER) {
        float val = atof(yytext);
        AVANCER
        return val;
    }
    else ERREUR_SYNTAXE
}

int main(void){                     /* Fonction principale */
    AVANCER			                /* initialiser jeton sur le premier car */
    float val = E();                /* axiome */
    if (jeton == FIN) {             /* expression reconnue et rien après */
        printf("\nMot reconnu\n"); 
        printf("Valeur = %f\n", val);
    }
    else ERREUR_SYNTAXE             /* expression reconnue mais il reste des car */
    return 0;
}
