SHELL:=/bin/bash

# bash will read this config file first
BASH_ENV=bash_env.sh
export BASH_ENV

# ----------------------------------------

all: _links
	$$ocamlc -c $$mls
	$$ocamlopt -c $$mls
	$$mk_cma -g -a -o $${libname}.cma $$cmos
	$$mk_cmxa -g -a -o $${libname}.cmxa $$cmxs
	$(MAKE) $$natives $$bytes


_links:
	`mk_links`
	touch $@

test:
	OCAMLRUNPARAM=b ./test.sh

_generated: FORCE
	$(MAKE) -C b_from_isa

mlis: 
	`mk_mlis`

_install:
	`mk_meta`
	`install`

_remove: 
	`remove`

_reinstall: 
	`remove`
	`install`


# ----------------------------------------

#	$$ocamlopt -g -linkpkg -o a.out $$mls # FIXME

%.native: %.ml btree.cmxa FORCE
	$$ocamlopt -g -linkpkg -o $*.native btree.cmxa $*.ml

%.byte: %.ml btree.cma FORCE
	$$ocamlc -g -linkpkg -o $*.byte btree.cma $*.ml

clean:
	rm -f *.{cmi,cmo,cmx,o} a.out *.cma *.cmxa *.a *.byte *.native 

real_clean: clean
	`rm_links`

FORCE:


