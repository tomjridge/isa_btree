#load "nums.cma";;

#require "ppx_deriving_yojson";;
#require "yojson";;

#load "btree.cma";;

(* to debug: execute with env OCAMLRUNPARAM=b ... *)

#show Btree;;

(* initialize a simple int int map *)

open Btree

module Int_int = struct 
  module Kv : KEY_VALUE_TYPES with type key=int and type value_t=int = struct
    type key = int[@@deriving yojson]
    type value_t = int[@@deriving yojson]
    let key_ord k1 k2 = Pervasives.compare k1 k2
    let equal_value = (=)
  end
end

module Consts : CONSTANTS = struct

  type min_size_t = Min_size.min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf
  let max_leaf_size = 4
  let max_node_keys = 4
  let min_leaf_size = 2
  let min_node_keys = 2

end

module Btree0 = Btree.Make(Consts)(Int_int.Kv)

let s0 = ref Btree0.empty

let s1 = Btree0.Insert.insert 1 1 !s0

let s2 = Btree0.Find.find 1 s1;;

let s3 = Btree0.Delete.delete 1 s1;;

let _ = 
  for i = 1 to 10 do
    s0 := Btree0.Insert.insert i (2*i) !s0
  done;;
    
let r1 = Btree0.tree_to_leaves !s0

let _ = 
  for i = 1 to 7 do
    s0 := Btree0.Insert.insert i (3*i) !s0
  done;;

let r2 = Btree0.tree_to_leaves !s0

let _ = 
  for i = 5 to 100 do
    s0 := Btree0.Insert.insert i (4*i) !s0
  done;;

let r3 = Btree0.tree_to_leaves !s0

let _ = 
  for i = 5 to 100 do
    s0 := Btree0.Delete.delete i !s0
  done;;

let Some s = !Btree0.Delete.last_state

(*
let x = !Our.any_ref;;

let x = ((Obj.magic x) : (Btree0.Isa_c.min_size_t option * Btree0.M.Tree.tree));;
let _ = Btree0.M.Tree.tree_to_yojson;;
let _ = Btree0.M.Tree.tree_to_yojson (snd x);;

let _ = (snd x) |> Btree0.M.Tree.tree_to_yojson |> Yojson.Safe.pretty_to_string |> print_endline;;

*)

(*


let _ = Btree0.Delete.check_state s

let Some(s,Some s') = !Btree0.Delete.last_trans;;

let _ = Btree0.Delete.check_state s

let _ = Btree0.Delete.check_state s'


let _ = Btree0.Delete.check_trans s (Some s')


let r4 = Btree0.tree_to_leaves !s0


let w = Btree0.M.Tree.wellformed_tree None !s0

;;

let _ = !Btree0.Delete.last_state;;
let Some(s,Some s') = !Btree0.Delete.last_trans;;

(* let w = s'|>Btree0.tree_to_subtrees *)

let dts_s_to_string s = (
  s|>Btree0.M.Delete_tree_stack.dts_state_t_to_yojson|>Yojson.Safe.pretty_to_string)

let j2 = s |> Btree0.M.Delete_tree_stack.dts_state_t_to_yojson;;

let _ = s |> dts_s_to_string |> print_endline

let _ = s' |> dts_s_to_string |> print_endline

*)
