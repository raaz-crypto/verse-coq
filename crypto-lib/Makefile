# The targets to build.

CC=gcc
ARCH=
IMPLS = chacha20/c/portable.c
ifdef TESTING
IMPLS += test/c/zerobuffer.c
.DEFAULT: main
main: main.c libverse.a
	gcc main.c libverse/verse.c libverse.a -o main
endif



SRC     = $(addprefix libverse/, ${IMPLS})
COQ_SRC = $(addsuffix .v, $(basename ${SRC}))
OBJ     = $(addsuffix .o, ${SRC})
VERSE   = coqc -R ../src Verse



.PHONY: clean


libverse/%c : %v
	mkdir -p $(dir $@)
	${VERSE} $< | ocaml -stdin > $@

%.c.o: %.c
	${CC} -Wall -Werror  -c -I libverse -include verse.h  -o $@ $<

libverse.a: ${OBJ}
	ar -cvq libverse.a ${OBJ}

libverse.tar.gz:
	make TESTING=yes clean
	make ${SRC}
	tar czv libverse -f libverse.tar.gz

clean:
	rm -f ${SRC} ${OBJ} libverse.a main libverse.tar.gz
