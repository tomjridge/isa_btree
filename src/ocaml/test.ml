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

module C_2222 : CONSTANTS = struct

  type min_size_t = Min_size.min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf
  let max_leaf_size = 2
  let max_node_keys = 2
  let min_leaf_size = 2
  let min_node_keys = 2

end

module T = Btree.Make(C_2222)(Int_int.Kv)

let range = Batteries.(0 -- 10 |> List.of_enum)

module S = Set.Make(struct type t = T.t let compare = Pervasives.compare end)

let test () = (
  let s = ref S.empty in
  let s' = ref (S.singleton T.empty) in
  (* next states from a given tree *)
  let step t = (
    (range|>List.map (fun x -> T.Insert.insert x x t)) @
    (range|>List.map (fun x -> T.Delete.delete x t))
  ) |> S.of_list
  in
  let _ = 
    while (not(S.equal !s !s')) do
      let d = S.diff !s' !s in
      let nexts : S.t list = d|>S.elements|>List.map step in
      let next = List.fold_left (fun a b -> S.union a b) S.empty nexts in
      s:=!s';
      s':=next;
      ()
    done
  in
  Printf.printf "Tests passed; num states explored: %d\n" (S.cardinal !s))
    

let _ = test ()
