########################################
#~ définitions
########################################

BIN=bin/fileCtrl bin/utilisateur

# liste des fichiers sources 
SRCS0=fileCtrl.c
SRCS1=utilisateur.c

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.c
	gcc -Wall -Iinclude -c $< -o $@

bin/fileCtrl: $(SRCS0:%.c=obj/%.o)
	gcc -o $@ $+ -lpthread

bin/utilisateur: $(SRCS1:%.c=obj/%.o)
	gcc -o $@ $+ -lpthread

clean:
	rm -f $(BIN) obj/*.o *~