CC=gcc
CFLAGS=-g
LEX=flex

build:
	$(LEX) md2html.l
	$(CC) $(CFLAGS) -o md2html lex.yy.c -lfl