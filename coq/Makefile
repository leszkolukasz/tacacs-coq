.PHONY: all coq build rebuild clean depend

COQC=coqc

COQFILES = $(wildcard *.v)

all: build

coq: $(COQFILES:.v=.vo)

build: depend coq

rebuild: clean build

.SUFFIXES: .v .vo .vok .vos

.v.vo:
	$(COQC) $<

.v.vok:
	$(COQC) $<

.v.vos:
	$(COQC) $<

clean:
	-rm -f *.vo[ks]
	-rm -f *.vo
	-rm -f *.glob
	-rm -f .*.aux
	-rm -f .coqdepend

.coqdepend: $(COQFILES)
	coqdep  *.v > .coqdepend

ifeq ($(MAKEDEPEND),)
depend: .coqdepend 
	make all MAKEDEPEND=yes
endif
ifeq ($(MAKEDEPEND),yes)
depend:
endif

-include .coqdepend
