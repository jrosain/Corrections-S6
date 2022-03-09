/**
 * fichier: analflex.l
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
/* Zone de définition */
%{
struct YYData {
    char *name;
    int val;
};
struct YYData yydata;

#define yymkdata(value) \
    yydata.val = value; yydata.name = #value; return value;

enum Tokens {
    KEYWORD = 300,
    LITENT,
    LITFLOT,
    ID,
    STRING,
    CHAR,
    OPEN_BLOC,
    CLOSE_BLOC,
    OPEN_PARENTHESIS,
    CLOSE_PARENTHESIS,
    END_INSTR,
    OPERATOR,
    AFFECTATION,
    COMPARATOR,
    ARG_SEP,
    OBJECT_ACCESSOR,
    ARRAY_OPEN_ACCESSOR,
    ARRAY_CLOSE_ACCESSOR,
    ADDRESS_ACCESSOR,
    TERNARY_FIRST,
    TERNARY_SECOND,
    NOT_RECOGNIZED = -1,
};
union {
    long int i;
    char *s;
    double f;
} yylval;
#define yymid \
    yylval.s = malloc(yyleng + 1); strcpy(yylval.s, yytext);
#define yyint \
    yylval.i = atol(yytext);
#define yydbl \
    yylval.f = atof(yytext);
%}
/* Règles. Les macros ne sont pas à reconnaître car elles sont gérées par un preprocess. */
%%
auto|break|case|char|const|continue|default|do|double|else|enum|extern|float|for|goto|if|inline|int|long|register|restrict|return|short|signed|sizeof|static|struct|switch|typedef|union|unsigned|void|volatile|while                       { yymid; yymkdata(KEYWORD) }
(0([0-7]*|[xX][0-9A-Fa-f]*))|([1-9][0-9]*)                              { yyint; yymkdata(LITENT) }
[A-Za-z_][A-Za-z0-9_]*                                                  { yymid; yymkdata(ID) }
([0-9]+\.[0-9]*|\.[0-9]+)([eEdD][\+-]?[0-9]+)?f?                        { yydbl; yymkdata(LITFLOT) }
([ \t\n\r\f]*|("//".*\n)|("/*"([^*]*"*"+[^*/])*[^*]*"*"+"/"))*          { /* filtrer */ }
(\"([^"]|\\\")*\")                                                      { yymkdata(STRING) }
('(\\(2([0-4][0-9]|5[0-5])|1[0-9]{2}|[1-9][0-9]|[0-9])|[^'])')          { yymkdata(CHAR) }
\{                                                                      { yymkdata(OPEN_BLOC) }
\}                                                                      { yymkdata(CLOSE_BLOC) }
\(                                                                      { yymkdata(OPEN_PARENTHESIS) }
\)                                                                      { yymkdata(CLOSE_PARENTHESIS) }
;                                                                       { yymkdata(END_INSTR) }
(\+|-|\*|\/%)                                                           { yymkdata(OPERATOR) }
=                                                                       { yymkdata(AFFECTATION) }
(!=|==|(<|>)=?)                                                         { yymkdata(COMPARATOR) }
,                                                                       { yymkdata(ARG_SEP) }
(\.|->)                                                                 { yymkdata(OBJECT_ACCESSOR) }
\[                                                                      { yymkdata(ARRAY_OPEN_ACCESSOR) }
\]                                                                      { yymkdata(ARRAY_CLOSE_ACCESSOR) }
&                                                                       { yymkdata(ADDRESS_ACCESSOR) }
\?                                                                      { yymkdata(TERNARY_FIRST) }
:                                                                       { yymkdata(TERNARY_SECOND) }
.                                                                       { yymkdata(NOT_RECOGNIZED) }
%%
/* Zone des fonctions C */
int main() {
    int j;
    while ((j = yylex()) != 0) {
        switch(j) {
        case KEYWORD:
        case ID:
            printf("Jeton : %i (%s) de valeur %s\n", yydata.val, yydata.name, yylval.s);
            break;
        case LITENT:
            printf("Jeton : %i (%s) de valeur %zu\n", yydata.val, yydata.name, yylval.i);
            break;
        case LITFLOT:
            printf("Jeton : %i (%s) de valeur %f\n", yydata.val, yydata.name, yylval.f);
            break;
        default :
            printf("Jeton : %i (%s) de lexeme %s\n", yydata.val, yydata.name, yytext);
            break;
        }
    }
}