all:
	bison -yd logic.y
	flex logic.l
	gcc -Wall -o logic y.tab.c lex.yy.c

debug:
	bison -ydtv regex.y
	flex logic.l
	gcc -Wall -o logic y.tab.c lex.yy.c