CC=gcc 
CFLAGS=-Wall -Iinclude -ansi

YACC=bison
YACCFLAGS=-ydtv

BIN=bin/expreg	bin/expamb
DIRG=@mkdir -p $(@D)

all: $(BIN)

clean: 
	rm y.output y.tab.*
	rm -rf bin

bin/expreg: expreg.y arbin.c
	$(DIRG)
	$(YACC) $(YACCFLAGS) expreg.y
	$(CC) $(CFLAGS) -o $@ y.tab.c arbin.c

bin/expamb: expamb.y arbin.c
	$(DIRG)
	$(YACC) $(YACCFLAGS) expamb.y
	$(CC) $(CFLAGS) -o $@ y.tab.c arbin.c