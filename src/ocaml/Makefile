SHELL:=/bin/bash

# bash will read this config file first
BASH_ENV=bash_env.sh
export BASH_ENV

all:
	$$ocamlc -c gen_isa.ml gen_our.ml
#	$$ocamlopt gen_btree.ml

# all2:
# 	ocamlc -c gen_btree.ml
# 	ocamlopt nums.cmxa gen_btree.ml

# rest:
# 	ocamlc -c -I /home/tr61/.opam/4.03.0/lib/ocaml nums.cma tmp.ml
# 	ocamlc -c -I /home/tr61/.opam/4.03.0/lib/ocaml nums.cma util.ml


clean:
	rm -f *.{cmi,cmo,cmx,o} a.out
