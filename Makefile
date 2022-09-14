COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat/vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: _CoqProject float_models.vo

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v > .depend

include .depend

clean:
	rm -f *.vo *.vok *.vos *.glob 

