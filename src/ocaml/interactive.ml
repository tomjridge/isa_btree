#load "nums.cma";;

#require "ppx_deriving_yojson";;
#require "yojson";;

#load "btree.cma";;

(* to debug: execute with env OCAMLRUNPARAM=b ... *)

#show Btree;;

(* initialize a simple int int map *)

open Btree


let j2 = s |> Btree0.M.Delete_tree_stack.dts_state_t_to_yojson;;

let _ = s |> dts_s_to_string |> print_endline

let _ = s' |> dts_s_to_string |> print_endline
