
BIN=bin/evaldesc bin/postdesc bin/arbindesc
DIR_GUARD=@mkdir -p $(@D)

default: $(BIN)

bin/evaldesc: evaldesc.c
	$(DIR_GUARD) 
	gcc -Wall -o $@ $+
bin/postdesc: postdesc.c
	$(DIR_GUARD) 
	gcc -Wall -o $@ $+
bin/arbindesc: arbindesc.c arbin.c
	$(DIR_GUARD) 
	gcc -Wall -o $@ $+