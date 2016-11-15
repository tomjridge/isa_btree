(* Testing the B-tree ---------------------------------------- *)

(* We concentrate on relatively small parameters *)

open Btree

module Int_int = struct 
  module Kv : KEY_VALUE_TYPES with type key=int and type value_t=int = struct
    type key = int[@@deriving yojson]
    type value_t = int[@@deriving yojson]
    let key_ord k1 k2 = Pervasives.compare k1 k2
    let equal_value = (=)
  end
end

module C_3322 : CONSTANTS = struct

  type min_size_t = Min_size.min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf
  let max_leaf_size = 3
  let max_node_keys = 3
  let min_leaf_size = 2
  let min_node_keys = 2

end

module T = Btree.Make(C_3322)(Int_int.Kv)

module S = Set.Make(struct type t = T.t let compare = Pervasives.compare end)

type action = Insert of int | Delete of int


(* we have a set of states s that we have already generated; 
   we have a set of states todo that we need to process; 
   for each todo, we apply all possible actions; 
   any new states that result are stored in "todo"; *)

(* if we hit an exception, we want to know what the input tree was,
   and what the command was *)

let input_tree = ref T.empty
let action = ref (Insert 0)

let test range = (
  let s = ref (S.singleton T.empty) in
  let todo = ref (S.singleton T.empty) in
  (* next states from a given tree *)
  let step t = (
    input_tree := t;
    (range|>List.map (fun x -> action:=Insert x; T.Insert.insert x x t)) @
    (range|>List.map (fun x -> action:=Delete x; T.Delete.delete x t))
  ) |> S.of_list
  in
  let _ = 
    Printf.printf "test: starting while";
    while (not(S.is_empty !todo)) do
      let nexts : S.t list = !todo|>S.elements|>List.map step in
      let next = List.fold_left (fun a b -> S.union a b) S.empty nexts in
      let new_ = S.diff next !s in
      s:=S.union !s new_;
      todo:=new_;
      print_string "."; flush_all ();
      ()
    done
  in
  Printf.printf "Tests passed; num states explored: %d\n" (S.cardinal !s))
