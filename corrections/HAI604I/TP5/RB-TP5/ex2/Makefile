########################################
#~ définitions
########################################

BIN=bin/semInit bin/semClient bin/suppr

# liste des fichiers sources
SRCS0=semInit.c
SRCS1=semClient.c
SRCS2=supprimeSem.c

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.c
	g++ -Wall -Iinclude -c $< -o $@

bin/semInit: $(SRCS0:%.c=obj/%.o)
	g++ -o $@ $+

bin/semClient: $(SRCS1:%.c=obj/%.o)
	g++ -o $@ $+

bin/suppr: $(SRCS2:%.c=obj/%.o)
	g++ -o $@ $+

clean:
	rm -f $(BIN) obj/*.o *~
