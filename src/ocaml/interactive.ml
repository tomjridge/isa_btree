#load "nums.cma";;

#require "ppx_deriving_yojson";;
#require "yojson";;
#require "batteries";;
#require "result";;

#mod_use "gen_isa.ml";;
#mod_use "our.ml";;

#mod_use "test.ml";;
#mod_use "pickle.ml";;
#mod_use "btree_api.ml";;
#mod_use "btree_util.ml";;
#mod_use "cache.ml";;

#mod_use "btree.ml";;
#mod_use "btree_simple.ml";;
#mod_use "map_int_int.ml";;

(* to debug: execute with env OCAMLRUNPARAM=b ... *)

