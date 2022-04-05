all:
	bison -yd regex.y
	gcc -o regex arbin.c y.tab.c

debug:
	bison -ydtv regex.y
	gcc -o regex arbin.c y.tab.c