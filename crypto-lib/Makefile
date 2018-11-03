# Currently supported primitives.
IMPLS = chacha20/c/portable \
        sha256/c/portable   \
        sha512/c/portable   \
	blake2b/c/portable  \
	blake2s/c/portable  \

ifdef CI  # On the continuous integration use the http for getting libverse.
	GIT_REPO=https://github.com/raaz-crypto/libverse.git # git repo where libverse reside
else
	GIT_REPO=git@github.com:raaz-crypto/libverse.git # git repo where libverse reside
endif

#############################################################
###    DO NOT change beyond this point unless you known   ###
###    what you are doing.                                ###
#############################################################

.DEFAULT_GOAL = libverse

ML_DIR      = mlsrc
ML_RAAZ_DIR = ${ML_DIR}/raaz

ML_SRC       = $(addprefix ${ML_DIR}/, $(addsuffix .ml, ${IMPLS}))
ML_RAAZ_SRC  = $(addprefix ${ML_RAAZ_DIR}/, $(addsuffix .ml, ${IMPLS}))
ML_SRC_DIRS  = $(addprefix ${ML_DIR}/, $(dir ${IMPLS}))
ML_RAAZ_DIRS = $(addprefix ${ML_RAAZ_DIR}/, $(dir ${IMPLS}))
CODE_DIRS    = $(addprefix libverse/, $(dir ${IMPLS}))
RAAZ_IMPLS     = $(shell runhaskell capitalize.hs ${IMPLS})
RAAZ_CODE_DIRS =  $(addprefix libverse/Raaz/Verse/,$(dir ${RAAZ_IMPLS}))



.PHONY: extract.v libverse clean verse dist-clean
.PHONY: dirs extract gen


dirs: # All the relevant directors.
	if [ ! -d libverse/.git ]; then \
		rm -rf libverse; \
		git clone ${GIT_REPO}; \
	fi
	mkdir -p ${ML_SRC_DIRS}
	mkdir -p ${ML_RAAZ_DIRS}
	mkdir -p ${CODE_DIRS}
	mkdir -p ${RAAZ_CODE_DIRS}

extract: verse dirs
	coqc -R ../src Verse extract.v

libverse: extract
	$(foreach mlprog, ${ML_SRC}, ocaml ${mlprog};)
	echo IMPLS=${IMPLS} > libverse/Implementations.mk
	$(foreach mlprog, ${ML_RAAZ_SRC}, ocaml ${mlprog};)

verse:
	make -C ..

clean:
	rm -f $(addprefix extract., vo glob)
	rm -rf mlsrc

dist-clean: clean
	make -C .. clean
