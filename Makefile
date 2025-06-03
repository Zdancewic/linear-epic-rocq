.PHONY: clean all rocq

COQPATHFILE=$(wildcard _CoqPath)

COQC="$(COQBIN)rocq" compile 
COQMAKEFILE="$(COQBIN)rocq" makefile
COQDEP="$(COQBIN)rocq" dep 
COQEXEC="$(COQBIN)rocq" top 
CP=cp

build: rocq

rocq: Makefile.rocq
	$(MAKE) -f Makefile.rocq

clean-rocq: _CoqProject
	if [ -e Makefile.rocq ] ; then $(MAKE) -f Makefile.rocq cleanall ; fi
	$(RM) Makefile.rocq Makefile.rocq.conf

Makefile.rocq: _CoqProject
	$(COQMAKEFILE) -f $< -o $@

all:
# Build the library before tests
	$(MAKE) rocq

clean: clean-rocq
	$(RM) _CoqProject

_CoqProject: $(COQPATHFILE) _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
	@ echo "# THIS IS AN AUTOMATICALLY GENERATED FILE" >> _CoqProject
	@ echo "# PLEASE EDIT _CoqConfig INSTEAD" >> _CoqProject
	@ echo >> _CoqProject
ifneq ("$(COQPATHFILE)","")
	@ echo "# including: _CoqPath"
	@ cat _CoqPath >> _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqConfig"
	@ cat _CoqConfig >> _CoqProject
