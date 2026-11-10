ROCQ ?= rocq
.DEFAULT_GOAL := all
.PHONY: all install uninstall check html clean

Makefile.rocq: _CoqProject Makefile
	$(ROCQ) makefile -f _CoqProject -o $@

all uninstall: Makefile.rocq
	$(MAKE) -f Makefile.rocq $@

install: all
	$(MAKE) -f Makefile.rocq install

html: all
	mkdir -p html
	$(ROCQ) doc -toc -html -Q theories MKNF -d html $(wildcard theories/*.v)

check: all
	$(ROCQ) check -silent -Q theories MKNF MKNF.Finite MKNF.Syntax MKNF.Semantics MKNF.Algorithms MKNF.MurderMystery

clean:
	@if test -f Makefile.rocq; then $(MAKE) -f Makefile.rocq clean; fi
	$(RM) Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	$(RM) -r html
