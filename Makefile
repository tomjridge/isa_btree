default: 
	$(MAKE) all

-include Makefile.ocaml


update_generated_doc: 
	cd ocaml && (ocamldoc_pyexpander isa_btree_intf.ml)
	cd ocaml && (ocamldoc_pyexpander make.ml)
	cd ocaml && (ocamldoc_pyexpander summary.t.ml > summary.ml)


test_main:=test_bin/test_main.exe

$(test_main):
	$(DUNE) build $(test_main)

run_tests: build $(test_main)
	time dune exec $(test_main) test_insert_many
	time dune exec $(test_main) test_insert_all
	time dune exec $(test_main) test_node_impl
	time dune exec $(test_main) test_leaf_impl
	time dune exec $(test_main) test_delete
	time dune exec $(test_main) test_exhaustive_2

isa_btree_doc: FORCE
	$(DUNE) build --only-packages isa_btree @doc
	rsync -vaz $(SRC)/* $(DST2); echo "docs built in $(DST2) but not promoted to docs/"

clean::
