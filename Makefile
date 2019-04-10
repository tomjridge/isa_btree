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

run_tests: build
	cd test && time dune exec test_main && time dune exec test_main no_asserts

all:
	$(MAKE) clean
	$(MAKE) build
	$(MAKE) run_tests
	$(MAKE) install
	$(MAKE) docs

SRC:=_build/default/_doc/_html
DST:=docs/ocamldoc
docs: FORCE
	$(DUNE) build @doc
	rm -rf $(DST)/*
	cp -R $(SRC)/* $(DST)

FORCE:
