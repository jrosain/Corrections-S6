########################################
#~ définitions
########################################

BIN=bin/client  bin/serveur


# liste des fichiers sources 
SRCS0=client.c
SRCS1=serveur.c

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.c
	gcc -Wall -Iinclude -c $< -o $@

bin/client: $(SRCS0:%.c=obj/%.o)
	gcc -o $@ $+

bin/serveur: $(SRCS1:%.c=obj/%.o)
	gcc -o $@ $+



clean:
	rm -f $(BIN) obj/*.o *~
