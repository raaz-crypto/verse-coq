# Currently supported primitives.
IMPLS = chacha20/c/portable \
        sha256/c/portable  \
        sha512/c/portable  \

ifdef CI  # On the continuous integration use the http for getting libverse.
	GIT_REPO=https://github.com/raaz-crypto/libverse.git # git repo where libverse reside
else
	GIT_REPO=git@github.com:raaz-crypto/libverse.git # git repo where libverse reside
endif

#############################################################
###    DO NOT change beyond this point unless you known   ###
###    what you are doing.                                ###
#############################################################

ML_DIR      = mlsrc/
ML_SRC      = $(addprefix ${ML_DIR}, $(addsuffix .ml, ${IMPLS}))
ML_SRC_DIRS = $(addprefix ${ML_DIR}, $(dir ${IMPLS}))
CODE_DIRS   = $(addprefix libverse/, $(dir ${IMPLS}))


.PHONY: extract.v libverse clean verse dist-clean

libverse: verse extract.v
	if [ ! -d libverse ]; then \
		git clone ${GIT_REPO};\
	fi
	mkdir -p ${ML_SRC_DIRS}
	mkdir -p ${CODE_DIRS}
	coqc -R ../src Verse extract.v
	$(foreach mlprog, ${ML_SRC}, ocaml ${mlprog};)
	echo IMPLS=${IMPLS} > libverse/Implementations.mk

verse:
	make -C ..

clean:
	rm -f $(addprefix extract., vo glob)
	rm -rf mlsrc

dist-clean: clean
	make -C .. clean
