/**
 * fichier: calcdesc.l
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
%{
#include <stdio.h>
#include <math.h>
struct YYData {
    char *name;
    int val;
};
struct YYData yydata;

#define yymkdata(value) \
    yydata.val = value; yydata.name = #value; return value;

enum Token {
    LITFLOT = 300,
};

double yylval;
%}
%%
(0|[1-9][0-9]*|[0-9]+\.[0-9]*|\.[0-9]+)([eEdD][\+-]?[0-9]+)?f?  { yylval = atof(yytext); yymkdata(LITFLOT) }
(.|\n)                                                          { return yytext[0]; }
%%

#define AVANCER { jeton = yylex(); numcar++; }
#define TEST_AVANCE(prevu) { if (jeton == (prevu)) AVANCER else ERREUR_SYNTAXE }
#define ERREUR_SYNTAXE { printf("\nMot non reconnu : %s\n", yytext); exit(1); } 

double E(); double R(double gauche); double T(); double S(double left); double F(); double G(); double H(double left);

int jeton;                                  /* caractère courant du flot d'entrée */
int numcar = 0;                             /* numero du caractère courant (jeton) */

double E() {                                   /* regle : E->TR */    
    return R(T());
}

double R(double left) {                           /* regle : R->+TR|-TR|epsilon */
    if (jeton == '+') {                     
        AVANCER
        return R(left + T());
    }
    if (jeton == '-') {                     
        AVANCER
        return R(left - T());
    }
    return left;
}

double T() {                                   /* regle : T->FS */
    return S(F());
}

double S(double left) {                           /* regle : S->*FS|/FS|epsilon */
    if (jeton == '*') {                     
        AVANCER
        return S(left * F());
    }
    if (jeton == '/') {
        AVANCER
        return S(left / F());
    }
    return left;
}

double F() {                                    /* regle : F->GH */
    return H(G());
}

double H(double left) {                         /* regle : ^GH|epsilon */
    if (jeton == '^') {
        AVANCER 
        double v = pow(left, H(G()));
        return v;
    }
    return left;
}

double G() {                                   /* regle : G->(E)|0|1|...|9 */
    if (jeton == '(') {                     
        AVANCER
        int res = E();
        TEST_AVANCE(')')
        return res;
    }
    else {
        if (jeton == LITFLOT) {
            double val = yylval;
            AVANCER
            return val;
        }
        else {
            ERREUR_SYNTAXE
        }
    }
}

int main(int argc, char **argv) {
    AVANCER
    double result = E();                    /* axiome */
    if (jeton == '\n') {                    /* expression reconnue et rien après */
        printf("Mot reconnu. Résultat: %f\n", result); 
    }
    else {
        ERREUR_SYNTAXE                      /* expression reconnue mais il reste des car */
    }
    return 0;
}