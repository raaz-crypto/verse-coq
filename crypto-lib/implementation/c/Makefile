PRIMS=Sha256 Sha512 \
       Blake2b Blake2s \
       ChaCha20 \
       Poly1305 \


##################################################################
GENERATED=$(wildcard .*.aux *.glob *.vo)
prims=$(foreach p,${PRIMS}, $(shell echo ${p} | tr A-Z a-z))

IMPL_FILES=$(patsubst %,libverse/%/c/portable.c, ${prims})
RAAZ_FILES=$(patsubst %,libverse/Raaz/Verse/%/C/Portable.hs, ${PRIMS})

EXTRACT=$(addsuffix .v, ${prims})
EXTRACT_RAAZ=$(addsuffix .v, ${PRIMS})

.PHONY: all clean

all: ${IMPL_FILES} ${RAAZ_FILES}

${EXTRACT}: extract.m4
	m4 -DPRIM=$(basename $@) extract.m4 > $@
${EXTRACT_RAAZ}: raaz.m4
	m4 -DPRIM=$(basename $@) raaz.m4 > $@

${IMPL_FILES}: libverse/%/c/portable.c : %.v
	mkdir -p $(dir $@)
	coqc -R ${VERSE} Verse $<  | indent ${INDENT_OPTS} > $@

${RAAZ_FILES}:  libverse/Raaz/Verse/%/C/Portable.hs : %.v
	mkdir -p $(dir $@)
	coqc -R ${VERSE} Verse $<  > $@
clean:
	rm -f ${EXTRACT}
	rm -f ${EXTRACT_RAAZ}
	rm -f ${RAAZ_FILES}
	rm -f ${IMPL_FILES}
	rm -rf libverse
	rm -f ${GENERATED}
