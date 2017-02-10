#!/bin/bash

function init()
{
    mkdir -p "coq-$COQ_VER"
    opam init --root="coq-$COQ_VER" --no-setup --yes
    eval `opam config env --root="coq-$COQ_VER"`
    opam install "coq.$COQ_VER" --yes
    coq_makefile -f _CoqProject -o Makefile

}

function build()
{
    eval `opam config env --root=coq-"$COQ_VER"`
    make
    make html

}

export COQ_VER=$2

case $1 in
    init) init; ;;
    build) build; ;;
    *) echo unkonwn command 
esac
