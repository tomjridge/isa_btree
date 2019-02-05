SHELL:=bash
DUNE:=dune

build:
	$(DUNE) build @install

install:
	$(DUNE) install

uninstall:
	$(DUNE) uninstall

clean:
	$(DUNE) clean

test: build
	cd test && dune exec test_main

doc: FORCE
	$(DUNE) build @doc

doc_install: doc
	rm -rf docs/ocamldoc/*
	cp -R _build/default/_doc/_html/* docs/ocamldoc

FORCE:
