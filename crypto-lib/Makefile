# Normally you need http repo but for release you need ssh repo.
GIT_REPO_HTTP=https://github.com/raaz-crypto/libverse.git
GIT_REPO_SSH=git@github.com:raaz-crypto/libverse.git


#############################################################
###    DO NOT change beyond this point unless you known   ###
###    what you are doing.                                ###
#############################################################

INDENT_OPTS=-linux
ROOT=$(abspath ..)
VERSE=${ROOT}/src
CRYPTOLIB=$(abspath .)
LIBVERSE=${CRYPTOLIB}/libverse

export ROOT
export VERSE
export CRYPTOLIB
export LIBVERSE
export INDENT_OPTS

SUBDIRS=implementation libverse

.PHONY: all subdirs test
.PHONY: clean subdirs-clean
.PHONY: ${SUBDIRS}


all: subdirs
subdirs: ${SUBDIRS}

## Subdirectories.

implementation:
		make -C implementation

libverse: implementation
	if [ ! -d libverse/.git ]; then \
		rm -rf libverse; \
		git clone ${GIT_REPO_HTTP}; \
	fi
	cp -rv $(wildcard implementation/c/libverse/*) libverse


## Cleaning action.
clean: subdirs-clean
	make -C implementation clean
	if [ -d libverse ]; then \
		make -C libverse clean; \
	fi

subdirs-clean:
	$(foreach dir, ${SUBDIRS}, make -C ${dir} clean;)

# Tests by compiling the c code in libverse.
test: libverse
	make -C libverse
