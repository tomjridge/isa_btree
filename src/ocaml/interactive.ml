#load "nums.cma";;
#load "btree.cma";;

#show Btree;;

(* initialize a simple int int map *)

open Btree

module Int_int = struct 
  module Kv : KEY_VALUE_TYPES with type key=int and type value_t=int = struct
    type key = int
    type value_t = int
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

let s2 = Btree0.Find.find 1 !s0;;

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


;;
