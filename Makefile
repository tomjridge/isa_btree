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

all:
	$(MAKE) clean
	$(MAKE) build
	$(MAKE) test
	$(MAKE) install
	$(MAKE) docs

SRC:=_build/default/_doc/_html
DST:=docs/ocamldoc
docs: FORCE
	$(DUNE) build @doc
	rm -rf $(DST)/*
	cp -R $(SRC)/* $(DST)

FORCE:
