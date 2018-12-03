set -a # export all vars
#set -x # debug


# NOTE in toplevel you need to #require "bos.top" and bos.setup;;

libname="isa_btree"
package_name="isa_btree"
required_packages="num,stdlib,ppx_deriving_yojson,ppx_deriving_yojson.runtime"  # may want a separate package for lwt 
description="$libname, OCaml version of Isabelle B-tree defns"

function clean() {
	rm -f *.cmi *.cmo *.cmx *.o *.x *.a *.cma *.cmxa *.cmt *.odoc
	find . -maxdepth 1 -type l -exec rm -f \{\} \;
  rm -f *.html *.css
  rm -f META
}

mls=`ocamldep -sort -one-line *.ml`

# doc ----------------------------------------------------

function mk_doc() {
    ocamlfind ocamldoc $PKGS $WARN -html $mls
    # FIXME assume package built and installed
}



# generic from here ----------------------------------------------------

# was in bash_env.common

PKGS="-package $required_packages"
SYNTAX=""

# 8~"pattern-matching is not exhaustive"; 
# 11~"this match case is unused";
# 26~"unused variable s2"
WARN="-w @f@p@u@s@40-8-11-26"

WITH_CMT="-bin-annot"

# -thread needed for core
  ocamlc="$DISABLE_BYTE ocamlfind ocamlc   -thread -g $WARN $PKGS $SYNTAX $WITH_CMT"
ocamlopt="$DISABLE_NTVE ocamlfind ocamlopt -thread -g $WARN $PKGS $SYNTAX $WITH_CMT"
ocamldep="ocamlfind ocamldep $PKGS"

mk_cma="$DISABLE_BYTE ocamlfind ocamlc"
mk_cmxa="$DISABLE_NTVE ocamlfind ocamlopt"

cmos="${mls//.ml/.cmo}"
cmxs="${mls//.ml/.cmx}"

natives="
"

# branch=`git symbolic-ref --short HEAD` 
# v=`date +'%F'`
# if [ "$branch" = "master" ]; then
#     package_name="${libname}"
# else 
#     package_name="${libname}_${branch}"
# fi


function mk_meta() {
v=`cat ../VERSION`
cat >META <<EOF
name="$package_name"
description="$description"
version="$v"
requires="$required_packages"
archive(byte)="$libname.cma"
archive(native)="$libname.cmxa"
EOF
}
