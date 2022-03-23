########################################
#~ définitions
########################################

BIN=bin/traitement
DIRG=@mkdir -p $(@D)

# liste des fichiers sources
SRCS0=traitement.c

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.c
	$(DIRG)
	gcc -Wall -Iinclude -c $< -o $@

bin/traitement: $(SRCS0:%.c=obj/%.o)
	$(DIRG)
	gcc -o $@ $+

clean:
	rm -f $(BIN) obj/*.o *~