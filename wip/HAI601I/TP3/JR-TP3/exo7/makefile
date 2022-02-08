CC=gcc
CFLAGS=-g
LEX=flex

build:
	$(LEX) delblancs.l
	$(CC) $(CFLAGS) -o delblancs lex.yy.c -lfl
