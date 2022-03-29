CC=gcc
CFLAGS=-ansi -Wall

LEX=flex
LEXLIB=-lfl
YACC=bison
YACCFLAGS=-ydtv

all: logic

clean:
	rm lex.yy.c y.tab.c y.tab.h logic

logic: logic.y logic.l
	$(YACC) $(YACCFLAGS) logic.y
	$(LEX) logic.l
	$(CC) $(CFLAGS) -o $@ y.tab.c lex.yy.c 