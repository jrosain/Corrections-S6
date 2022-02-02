%{ /* analflex.l */
/* ZONE DE DEFINITION (OPTIONNELLE) */

/* globale, contient une seule des trois valeurs à un instant t */
union {
    int i;
    double d;
    char* s;
} yylval;
/*  globale, contient le nom des jetons récupéré grâce aux macros  */
char* yyjeton;
/*  liste des jetons et leur numéro associé  */
#define MOTCLE 300
#define LITENT 303
#define LITFLOT 304
#define ID 305
#define OUVERTURE 306
#define FERMETURE 307
#define PONCTUATION 308
#define OPERATION 309
#define SAIT_PAS -1
/*  macros pour récupérer la valeur sémantique, et le nom du jeton */
#define yystr(entree) \
yylval.s=(char*)malloc(strlen(yytext)+1);strcpy(yylval.s, yytext);yyjeton = #entree;
#define yyint(entree) \
yylval.i = atoi(yytext);yyjeton = #entree;
#define yyflt(entree) \
yylval.d = atof(yytext);yyjeton = #entree;
#define yyjet(entree) \
yyjeton = #entree;

/* ZONE DES REGLES apres le double pourcent (OBLIGATOIRE) */
%}
%%
if|then|else|throw|while                        {yystr(MOTCLE);         return MOTCLE;}
0[^0-9]|[1-9][0-9]*                             {yyint(LITENT);         return LITENT;}
0[1-9]+                                         {yyint(LITENT);         return LITENT;}
0x[1-9A-Fa-f]+                                  {yyint(LITENT);         return LITENT;}
[a-zA-Z]+[0-9a-zA-z_]*                          {yystr(ID);             return ID;}
([0-9]+\.|\.[0-9])[0-9]*([eE][-+]?[0-9]+)?      {yyflt(LITFLOT);        return LITFLOT;}
[ \n\t]*                                        {/* filtrer */}
\/((\/.*\n)|(\*([^\*\/]|(\*[^\/])|\/)*\*\/))    {/* filtrer */}
[\(\{\[]                                        {yystr(OUVERTURE);      return OUVERTURE;}
[\)\}\]]                                        {yystr(FERMETURE);      return FERMETURE;}
[,\';:\\\""\|!\^\?]                             {yystr(PONCTUATION);    return PONCTUATION;}
[=\*+-/%#]                                      {yystr(OPERATION);      return OPERATION;}
.|\n                                            {yystr(SAIT_PAS);       return SAIT_PAS;}
%%

/* ZONE DES FONCTIONS C */
int main() {
    int j; 
    char *invite = "Saisissez un(des) mot(s) reconnu par l'AFD suivi de EOF (CTRL-D) SVP : ";
    printf("%s",invite);
    while ((j=yylex())!=0) {
        switch(j) {
            case MOTCLE:
            case ID:
            case OUVERTURE:
            case FERMETURE:
            case PONCTUATION:
            case OPERATION:
            case SAIT_PAS:
                printf("\nJeton : %i (%s); (val: %s) (lexeme %s)",j,yyjeton,yylval.s,yytext);
                break;
            case LITENT:
                printf("\nJeton : %i (%s); (val: %i) (lexeme %s)",j,yyjeton,yylval.i,yytext);
                break;
            case LITFLOT:
                printf("\nJeton : %i (%s); (val: %lf) (lexeme %s)",j,yyjeton,yylval.d,yytext);
                break;
        }
    }
    printf("\n");
}