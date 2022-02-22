BIN=bin/calcdesc
SRC=calcdesc.l 
DIR_GUARD=@mkdir -p $(@D)
CC=gcc
CFLAGS=-Wall -Iinclude

default: $(BIN)

%.c: %.l
	flex $^

bin/calcdesc: $(SRC:%.l=%.c)
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ lex.yy.c -lfl -lm