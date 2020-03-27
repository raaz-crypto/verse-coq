IMPLS=sha256 sha512 \
       blake2b blake2s \
       chacha20 \
       poly1305 \

EXTRACT=$(addsuffix .v, ${IMPLS})

.PHONY: all clean

all: ${EXTRACT}
	$(foreach prim, ${EXTRACT},\
	coqc -R ${VERSE} Verse ${prim} | indent ${INDENT_OPTS} \
	> ${LIBVERSE}/$(basename ${prim})/c/portable.c; )

${EXTRACT}: extract.m4
	m4 -DPRIM=$(basename $@) extract.m4 > $@

clean:
	rm -f ${EXTRACT}
