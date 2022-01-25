SOURCES  = $(shell find . -type f -name '*.c')
HEADERS  = $(shell find . -type f -name '*.h')

C = @gcc
FLAGS = -Wall 

%.o:%.c 
	$(C) -c $(FLAGS) $< -o $@
analex: $(SOURCES:%.c=%.o)
	$(C) $(FLAGS) $^ -o $@

clean:
	@rm -f *.o
	@rm -f analex