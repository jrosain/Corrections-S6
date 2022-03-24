BIN=bin/RGBtoY	bin/EQM	bin/RGBtoYCbCr	bin/YCbCrtoRGB	bin/inversion	bin/modifY
CC=gcc
CFLAGS=-Wall -Iinclude
DIR_GUARD=@mkdir -p $(@D)

default: $(BIN)

bin/RGBtoY: RGBtoY.cpp 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/EQM: EQM.cpp 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+ -lm

bin/RGBtoYCbCr: RGBtoYCbCr.cpp 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/YCbCrtoRGB: YCbCrtoRGB.c 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/inversion: inversion.c 
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

bin/modifY: modifY.c
	$(DIR_GUARD)
	$(CC) $(CFLAGS) -o $@ $+

clean:
	rm -rf bin