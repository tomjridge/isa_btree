SHELL:=/bin/bash

# bash will read this config file first
BASH_ENV=bash_env.sh
export BASH_ENV

# ----------------------------------------

all: _links
	$$ocamlc -c $$mls
	$$ocamlopt -c $$mls
	$$mk_cma -g -a -o btree.cma $$cmos
	$$mk_cmxa -g -a -o btree.cmxa $$cmxs
	$(MAKE) $$natives $$bytes


_links:
	`mk_links`
	touch $@

test:
	OCAMLRUNPARAM=b ./test.sh

_generated: FORCE
	$(MAKE) -C b_from_isa

# ----------------------------------------

#	$$ocamlopt -g -linkpkg -o a.out $$mls # FIXME

%.native: %.ml btree.cmxa
	$$ocamlopt -g -linkpkg -o $*.native btree.cmxa $*.ml

%.byte: %.ml btree.cma
	$$ocamlc -g -linkpkg -o $*.byte btree.cma $*.ml

clean:
	rm -f *.{cmi,cmo,cmx,o} a.out *.cma *.cmxa *.a *.byte *.native 

real_clean: clean
	`rm_links`

FORCE:


