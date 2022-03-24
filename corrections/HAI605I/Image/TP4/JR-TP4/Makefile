BIN=bin/norme_gradient 	bin/hysteresis	bin/gaussien
CC=gcc
CFLAGS=-Wall -Iinclude
DIR_GUARD=@mkdir -p $(@D)

default: $(BIN)

bin/norme_gradient: norme_gradient.cpp 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+ -lm

bin/hysteresis: hysteresis.cpp 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/gaussien: gaussien.cpp 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

clean:
	rm -rf bin