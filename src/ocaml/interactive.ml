#load "nums.cma";;

#require "ppx_deriving_yojson";;
#require "yojson";;
#require "batteries";;
#require "result";;

#mod_use "gen_isa.ml";;
#mod_use "our.ml";;
#mod_use "btree.ml";;
#mod_use "test.ml";;

(* to debug: execute with env OCAMLRUNPARAM=b ... *)

open Test

let _ = Test.T.M.Json.dts_state_to_string 

let _ = Test.T.M.Tree.wellformed_tree


(*

let _ = Test.test [0;1;2;3;4;5;6;7;8;9]

let x = !Our.any_ref


let (ms,t) = ((Obj.magic x):Test.T.Isa_c.min_size_t option * Test.T.M.Tree.tree)

let Some(s,s') = !Test.T.Insert.last_trans

let t = !Test.input_tree

let action = !Test.action

*)
    
