########################################
#~ définitions
########################################

# Executables à générer
BIN=bin/grey bin/color

# liste des fichiers sources 
SRCS0=grey.cpp
SRCS1=color.cpp

default: $(BIN)

########################################
#~ regles pour l'executable
########################################

obj/%.o: %.cpp
	g++ -Wall -Iinclude -c $< -o $@

bin/grey: $(SRCS0:%.cpp=obj/%.o)
	g++ -o $@ $+

bin/color: $(SRCS1:%.cpp=obj/%.o)
	g++ -o $@ $+

clean:
	rm -f $(BIN) obj/*.o *~
