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

.PHONY: all clean root

all: root
	make -C implementation

root:
	make -C ${ROOT}
clean:
	make -C implementation clean
