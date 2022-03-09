BIN=bin/ddp	bin/repartition	bin/egalisation
CC=gcc
CFLAGS=-Wall -Iinclude
DIR_GUARD=@mkdir -p $(@D)

default: $(BIN)

bin/ddp: ddp.c 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/repartition: repartition.c 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/egalisation: egalisation.c 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

clean:
	rm -rf bin