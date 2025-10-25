CC=clang
RMF=rm -rf
CFLAGS=-g -O3 -lmimalloc -flto
SRC=main.c

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Darwin)
    CFLAGS += -lpthread -Wl,-stack_size -Wl,0x8000000
endif
ifeq ($(UNAME_S), Linux)
    CFLAGS += -pthread
endif


all: main.out

fresh: clean main.out

main.out: $(SRC) $(LIB)
	$(CC) $(CFLAGS) $^ -o $@

clean:: ; $(RMF) *.dSYM
clean:: ; $(RMF) *.gch
clean:: ; $(RMF) *.out

cleanall: clean
	$(RMF) prelude.h
	$(RMF) main.h
	$(RMF) main.c
