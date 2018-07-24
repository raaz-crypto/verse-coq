# The targets to build.

CC=gcc
ARCH=
IMPLS = chacha20/c/portable.c

ifdef TESTING
IMPLS += test/c/zerobuffer.c
.DEFAULT: main
main: main.c libverse.a
	gcc main.c lib/verse.c libverse.a -o main
endif



SRC     = $(addprefix lib/, ${IMPLS})
COQ_SRC = $(addsuffix .v, $(basename ${SRC}))
OBJ     = $(addsuffix .o, ${SRC})
VERSE   = coqc -R ../src Verse



.PHONY: clean


lib/%c : %v
	mkdir -p $(dir $@)
	${VERSE} $< | ocaml -stdin > $@

%.c.o: %.c
	${CC} -Wall -Werror  -c -I lib -include verse.h  -o $@ $<

libverse.a: ${OBJ}
	ar -cvq libverse.a ${OBJ}

clean:
	rm -f ${SRC} ${OBJ} libverse.a main
