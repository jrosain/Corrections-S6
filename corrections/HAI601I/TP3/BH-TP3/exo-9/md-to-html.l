/* Zone de définition */

%{
    enum TypeJeton {
        EMPTY_LINE = 1,
        NEW_LINE,
        PUCE,
        INDENTATION,
        ANY_CHAR,
    };
%}

/* Zone des règles */

%%
^[\n \t]*\n     { return EMPTY_LINE; }
\n              { return NEW_LINE; }
[\*\-]          { return PUCE; }
(\t|\ \ \ \ )   { return INDENTATION; }
.               { return ANY_CHAR; } // Les autres caractères
%%

/* Zone des fonctions C */

int main(int argc, char** argv) {
    if (argc != 3) {
        printf("Utilisation : %s in.md out.html\n", argv[0]);
        exit(1);
    }
    
    yyin = fopen(argv[1], "r");
    yyout = fopen(argv[2], "w");

    int j;
    int last_indent = -1;
    int actual_indent = 0;
    int begin_line = 1;

    while ((j=yylex()) != 0) {
        switch(j) {
            case INDENTATION:
                actual_indent += 1;
                break;
            case PUCE:
                if (begin_line) {
                    if (last_indent >= 0) {
                        fprintf(yyout, "</li>");
                    }
                    if (last_indent < actual_indent) {
                        for (int i = last_indent; i < actual_indent; ++i) {
                            fprintf(yyout, "<ul>");
                        }
                    }
                    else if (last_indent > actual_indent) {
                        for (int i = actual_indent; i < last_indent; ++i) {
                            fprintf(yyout, "</ul>");
                        }
                    }
                    fprintf(yyout, "<li>");

                    last_indent = actual_indent;
                }
                begin_line = 0;
                break;
            case NEW_LINE:
                begin_line = 1;
                actual_indent = 0;
                break;
            case ANY_CHAR:
                begin_line = 0;
                break;
            case EMPTY_LINE:
                if (last_indent > -1) {
                    fprintf(yyout, "</li>");
                    for (int i = -1; i < last_indent; ++i) {
                        fprintf(yyout, "</ul>");
                    }
                }
                last_indent = -1;
        }

        if (j != PUCE) {
            ECHO;
        }
    }
    
    return 0;
}