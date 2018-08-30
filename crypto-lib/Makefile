# Currently supported primitives.
IMPLS = chacha20/c/default \
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


.PHONY: extract.v libverse clean


libverse: extract.v
	if [ ! -d libverse ]; then \
		git clone ${GIT_REPO};\
	fi
	mkdir -p ${ML_SRC_DIRS}
	mkdir -p ${CODE_DIRS}
	coqc -R ../src Verse extract.v
	$(foreach mlprog, ${ML_SRC}, ocaml ${mlprog};)
	echo IMPLS=${IMPLS} > libverse/Implementations.mk

extract.v: extract.m4
	($(foreach imp,${IMPLS}, echo 'EXTRACT('${imp}')';)) \
	| m4 -DVERSION="${VERSION}" -DVERSE_DIR=libverse -DML_DIR=${ML_DIR} extract.m4 - \
	> extract.v

clean:
	rm -f $(addprefix extract., v vo glob)
	rm -rf mlsrc
