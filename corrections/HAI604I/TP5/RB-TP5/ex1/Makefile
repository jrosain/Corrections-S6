########################################
#~ définitions
########################################

BIN=bin/Pi  bin/Pctrl bin/suppr

# liste des fichiers sources
SRCS0=Pi.cc
SRCS1=Pctrl.cc
SRCS3=supprimeFile.cc

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.cc
	g++ -Wall -Iinclude -c $< -o $@

bin/Pi: $(SRCS2:%.c=obj/%.o) $(SRCS0:%.c=obj/%.o)
	g++ -o $@ $+

bin/Pctrl: $(SRCS1:%.c=obj/%.o)
	g++ -o $@ $+

bin/suppr: $(SRCS3:%.c=obj/%.o)
	g++ -o $@ $+



clean:
	rm -f $(BIN) obj/*.o *~
