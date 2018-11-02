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
.PHONY: mldir codedir extract gen


mldir: # The directory where the ocaml source is to be extracted.
	mkdir -p ${ML_SRC_DIRS}
	mkdir -p ${ML_RAAZ_DIRS}

codedir:  # the directory where the ocaml code creates files.
	mkdir -p ${CODE_DIRS}
	mkdir -p ${RAAZ_CODE_DIRS}

extract: mldir
	coqc -R ../src Verse extract.v

libverse: verse codedir extract
	if [ ! -d libverse ]; then \
		git clone ${GIT_REPO};\
	fi
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
