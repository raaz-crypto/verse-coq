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

.PHONY: all clean implementation root update-libverse gitrepos  compile-test

all: implementation

implementation: root
	make -C implementation

root:
	make -C ${ROOT}
clean:
	make -C implementation clean
	if [ -d libverse ]; then \
		make -C libverse clean; \
	fi

# This command only tests whether the generated c codes compiles. No
# other interesting tests are present in the libverse library.

compile-test: gitrepos
	make -C libverse

update-libverse: implementation gitrepos
	cp -rv $(wildcard implementation/c/libverse/*) libverse

gitrepos: implementation
	if [ ! -d libverse/.git ]; then \
		rm -rf libverse; \
		git clone ${GIT_REPO_HTTP}; \
	fi
