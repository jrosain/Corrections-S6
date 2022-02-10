CC=gcc
CFLAGS=-Wall

all: inverse filtre_flou1 filtre_flou2 filtre_flou

inverse:
	$(CC) $(CFLAGS) -o bin/inverse inverse.cpp

filtre_flou1:
	$(CC) $(CFLAGS) -o bin/filtre_flou1 filtre_flou1.cpp

filtre_flou2:
	$(CC) $(CFLAGS) -o bin/filtre_flou2 filtre_flou2.cpp

filtre_flou:
	$(CC) $(CFLAGS) -o bin/filtre_flou filtre_flou.cpp