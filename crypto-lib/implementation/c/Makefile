IMPLS=sha256 sha512 \
       blake2b blake2s \
       chacha20 \
       poly1305 \

implpath = $(1)/c/portable.c

IMPL_FILES= $(foreach prim, ${IMPLS}, $(call implpath, ${prim}))
IMPL_FULL_PATH= $(addprefix ${LIBVERSE}/, ${IMPL_FILES})

LIBVERSE_IMPL_MK=${LIBVERSE}/Implementations.mk

EXTRACT=$(addsuffix .v, ${IMPLS})

.PHONY: all clean ${LIBVERSE_IMPL_MK}




all: ${IMPL_FULL_PATH} ${LIBVERSE_IMPL_MK}

${EXTRACT}: %.v : extract.m4
	m4 -DPRIM=$(basename $@) extract.m4 > $@

${IMPL_FULL_PATH}: ${LIBVERSE}/%/c/portable.c : %.v
	coqc -R ${VERSE} Verse $<  | indent ${INDENT_OPTS} > $@

${LIBVERSE_IMPL_MK}:
	echo "IMPLS=${IMPL_FILES}" > $@

clean:
	rm -f ${EXTRACT}
