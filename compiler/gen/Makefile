CC=clang
RMF=rm -rf
SRC=main.c

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Darwin)
    MIMALLOC_PREFIX := $(shell brew --prefix mimalloc)
    CFLAGS += -lpthread -Wl,-stack_size -Wl,0x8000000
endif
ifeq ($(UNAME_S), Linux)
    MIMALLOC_PREFIX := $(shell pkg-config --variable=prefix mimalloc)
    CFLAGS += -pthread
endif

CFLAGS += -g -O3 -flto -I$(MIMALLOC_PREFIX)/include
MIMALLOC_OBJ := $(MIMALLOC_PREFIX)/lib/mimalloc.o


all: main.out

fresh: clean main.out

main.out: $(SRC) $(LIB)
	$(CC) $(CFLAGS) $^ $(MIMALLOC_OBJ) -o $@

clean:: ; $(RMF) *.dSYM
clean:: ; $(RMF) *.gch
clean:: ; $(RMF) *.out

cleanall: clean
	$(RMF) prelude.h
	$(RMF) main.h
	$(RMF) main.c
