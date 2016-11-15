SHELL:=/bin/bash

# bash will read this config file first
BASH_ENV=bash_env.sh
export BASH_ENV

all:
	$$ocamlc -c $$mls
	$$mk_cma -g -a -o btree.cma $$cmos
#	$$ocamlc -g -linkpkg -o a.out btree.cma test.ml - just use test.sh

clean:
	rm -f *.{cmi,cmo,cmx,o} a.out 

# test:


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
	/tmp/l/git/scripts/ocaml/btree_munge.ml
	cp ../generated/$@ .

# make this after editing our.ml
our.diff: backup FORCE
	-diff -u gen_our.ml our.ml >$@

our.ml: backup gen_our.ml FORCE
	patch -i our.diff gen_our.ml -o $@

