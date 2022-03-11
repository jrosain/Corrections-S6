BIN=bin/exo1  bin/rdv	bin/traitementImage

# liste des fichiers sources 
EX1=exo1.c 
RDV=rdv.c
IMG=traitementImage.c
DIR_GUARD=@mkdir -p $(@D)
CC=gcc 
CFLAGS=-Wall -Iinclude

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.c
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -c $< -o $@

bin/exo1: $(EX1:%.c=obj/%.o)
	$(DIR_GUARD)
	$(CC) -o $@ $+ obj/calculC.o -lpthread

bin/rdv: $(RDV:%.c=obj/%.o)
	$(DIR_GUARD)
	$(CC) -o $@ $+ obj/calculC.o -lpthread

bin/traitementImage: $(IMG:%.c=obj/%.o)
	$(DIR_GUARD)
	$(CC) -o $@ $+ obj/calculC.o -lpthread
	
clean:
	rm -f $(BIN) obj/*.o *~
