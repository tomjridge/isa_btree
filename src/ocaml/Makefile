SHELL:=/bin/bash

# bash will read this config file first
BASH_ENV=bash_env.sh
export BASH_ENV

all:
	$$ocamlc -c $$mls
	$$ocamlopt -c $$mls
	$$mk_cma -g -a -o btree.cma $$cmos
	$$mk_cmxa -g -a -o btree.cmxa $$cmxs
	$(MAKE) $$natives $$bytes

#	$$ocamlopt -g -linkpkg -o a.out $$mls # FIXME

%.native: %.ml btree.cmxa
	$$ocamlopt -g -linkpkg -o $*.native btree.cmxa $*.ml

%.byte: %.ml btree.cma
	$$ocamlc -g -linkpkg -o $*.byte btree.cma $*.ml

clean:
	rm -f *.{cmi,cmo,cmx,o} a.out *.cma *.cmxa *.a *.byte *.native

test:
	OCAMLRUNPARAM=b ./test.sh


real_clean: clean
	mv *.bak.* /tmp

FORCE:


# dealing with generated code ----------------------------------------

# gen_our.ml - copy of isa modules
# our.ml - edited gen_our.ml.bak to add functorization
# our.diff - diff from gen_our.ml.bak to our; reapply when gen_our changes

backup: FORCE
	cp gen_our.ml `new_bak gen_our.ml`
	cp our.ml `new_bak our.ml`
	cp our.diff `new_bak our.diff`

gen_our.ml: backup FORCE
	btree_munge2
	cp ../generated/$@ .

# make this after editing our.ml
# https://forums.anandtech.com/threads/best-practices-for-creating-patch-with-diff.2264468/
our.diff: backup FORCE
	-diff -u3 -p gen_our.ml our.ml >$@



our.ml: backup gen_our.ml FORCE
	patch -i our.diff gen_our.ml -o $@

