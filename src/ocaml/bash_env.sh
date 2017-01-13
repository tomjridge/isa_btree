set -a # export all vars
# set -x # debug

function new_bak() {
    local n=1 
    while [ -f "$1.bak.$n" ]; do ((++n)); done
    echo "$1.bak.$n"
}

root=$(realpath $(dirname $BASH_SOURCE))/../..

 # if using nix, this may not be present
test -f $root/config.sh && source $root/config.sh

PKGS="-package num,yojson,ppx_deriving_yojson,batteries,bos.setup \
  -package ppx_assert,ppx_assert.runtime-lib,sexplib,core,lru-cache,tjr_lib"

SYNTAX="" # "-syntax camlp4o" # simplify: use for every file
FLGS="-g -thread"

# 8~"pattern-matching is not exhaustive"; 
# 11~"this match case is unused";
# 26~"unused variable s2"
WARN="-w @f@p@u@s@40-8-11-26"

# these include syntax, so should work on all files; may be overridden in ocamlc.sh
  ocamlc="$DISABLE_BYTE ocamlfind ocamlc   $FLGS $WARN $PKGS $SYNTAX"
ocamlopt="$DISABLE_NTVE ocamlfind ocamlopt $FLGS $WARN $PKGS $SYNTAX"
ocamldep="ocamlfind ocamldep $PKGS"

mk_cma="$DISABLE_BYTE ocamlfind ocamlc $FLGS "
mk_cmxa="$DISABLE_NTVE ocamlfind ocamlopt $FLGS"


mls="gen_isa.ml our.ml btree_util.ml btree.ml in_mem.ml \
  block_device.ml int_int_store.ml bytestore.ml"

# test_in_mem.ml  test_ii.ml

cmos="${mls//.ml/.cmo}"
cmxs="${mls//.ml/.cmx}"

natives="test_in_mem.native test_ii.native"

bytes="test_in_mem.byte test_ii.native"

