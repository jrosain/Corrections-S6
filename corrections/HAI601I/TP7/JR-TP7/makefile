BIN=bin/expreg
DIR_GUARD=@mkdir -p $(@D)
SRC=$(shell ls *.c)

default: $(BIN)

bin/expreg: $(SRC)
	$(DIR_GUARD) 
	gcc -Wall -o $@ $+