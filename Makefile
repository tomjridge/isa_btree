SHELL:=bash
DUNE:=dune
# or something like DUNE:=dune build --only-packages isa_btree @doc

build:
	$(DUNE) build @install

install:
	$(DUNE) install

uninstall:
	$(DUNE) uninstall

clean:
	$(DUNE) clean

test_main:=test_bin/test_main.exe

$(test_main):
	$(DUNE) build $(test_main)

run_tests: build $(test_main)
	time dune exec $(test_main) test_insert_many
	time dune exec $(test_main) test_insert_all
#	time dune exec $(test_main) test_node_impl
#	time dune exec $(test_main) test_leaf_impl
#	time dune exec $(test_main) test_delete
#	time dune exec $(test_main) test_exhaustive_2


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
#	cd docs && tree -H . -L 1 --charset utf-8 >index.html

isa_btree_doc: FORCE
	$(DUNE) build --only-packages isa_btree @doc
	rsync -vaz $(SRC)/* $(DST2); echo "docs built in $(DST2) but not promoted to docs/"

FORCE:
