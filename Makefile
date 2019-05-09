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
	$(MAKE) install
	$(MAKE) docs
#	$(MAKE) run_tests

SRC:=_build/default/_doc/_html
DST:=docs/ocamldoc
DST2:=/tmp/isa_btree
docs: FORCE
	$(DUNE) build @doc
	@if [ ! -z "$$PROMOTE_DOCS" ]; then rm -rf $(DST)/* ; cp -R $(SRC)/* $(DST); echo "docs built and promoted to docs/"; else \
	  rsync -vaz $(SRC)/* $(DST2); echo "docs built in $(DST2) but not promoted to docs/"; fi

promote_docs: FORCE
	PROMOTE_DOCS=true $(MAKE) docs
	cd docs && tree -H . -L 1 --charset utf-8 >index.html
FORCE:
