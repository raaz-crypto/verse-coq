.DEFAULT_GOAL=build
SUBDIRS=test crypto-lib

.PHONY: all build clean ${SUBDIR} subdirs-clean html

## The targets that are defined here.
all: build crypto-lib

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

build: Makefile.coq
	$(MAKE) -f Makefile.coq

test: build
	make -C test all
	make -C crypto-lib test

crypto-lib: build
	make -C crypto-lib

## Cleaning.
clean: subdirs-clean
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

subdirs-clean:
	$(foreach dir, ${SUBDIRS}, make -C ${dir} clean;)
	$(foreach dir, ${SUBDIRS} src, rm -f `find ${dir} -name '.*.aux'`)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

Makefile _CoqProject:;


## All other targets come form what is generated via coq_makefile.

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
