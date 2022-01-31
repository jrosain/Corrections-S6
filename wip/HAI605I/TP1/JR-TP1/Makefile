########################################
#~ définitions
########################################

# Executables à générer
BIN=bin/tp1

# liste des fichiers sources 
SRCS0=main.cpp

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.cpp
	g++ -Wall -Iinclude -c $< -o $@

bin/tp1: $(SRCS0:%.cpp=obj/%.o)
	g++ -o $@ $+

clean:
	rm -f $(BIN) obj/*.o *~
