SHELL:=/bin/bash

# bash will read this config file first
BASH_ENV=bash_env.sh
export BASH_ENV

all: _links
	$$ocamlc -c $$mls
	$$ocamlopt -c $$mls
	$$mk_cma -g -a -o btree.cma $$cmos
	$$mk_cmxa -g -a -o btree.cmxa $$cmxs
	$(MAKE) $$natives $$bytes

_links:
	`mk_links`
	touch $@

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
	-mv *.bak.* /tmp
	`rm_links`
	rm -f _generated

FORCE:


# dealing with generated code ----------------------------------------

# FIXME this needs to be redone

# gen_isa.ml - needed by our.ml; generated code, isabelle specific
# gen_our.ml - generated code, our modules
# gen_our.ml.bak - copy of above
# our.ml - edited gen_our.ml.bak to add functorization
# our.diff - diff from gen_our.ml.bak to our; reapply when gen_our changes

# save old versions
_backup: FORCE
	cp gen_our.ml `new_bak gen_our.ml`
	cp our.ml `new_bak our.ml`
	cp our.diff `new_bak our.diff`

# call munger to split generated code into gen_isa and gen_our
_generated: backup FORCE
	btree_munge2
	cp ../generated/gen_our.ml b_from_isa
	cp ../generated/gen_isa.ml b_from_isa
	touch _generated

# make this after editing our.ml
# https://forums.anandtech.com/threads/best-practices-for-creating-patch-with-diff.2264468/
our.diff: _backup FORCE
	-diff -u3 -p gen_our.ml our.ml >$@



our.ml: _backup _generated FORCE
	patch -i our.diff gen_our.ml -o $@

