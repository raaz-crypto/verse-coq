#!/bin/bash

COQ_BUILD_DIR="coq-$COQ_VER"

function init()
{
    mkdir -p "coq-$COQ_VER"
    opam init --root="$COQ_BUILD_DIR" --no-setup --yes
    eval `opam config env --root="$COQ_BUILD_DIR"`
    coqtop -v
    opam install "coq.$COQ_VER" --yes
    coq_makefile -f _CoqProject -o Makefile

}

function build()
{
    eval `opam config env --root="$COQ_BUILD_DIR"`
    coqtop -v
    make
    make html

}


case $1 in
    init) init; ;;
    build) build; ;;
    *) echo "$0:error:" unknown command "$1" 
esac
