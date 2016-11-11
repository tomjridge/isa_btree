open Gen_isa

module Min_size = struct 
  type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf
end

module type CONSTANTS = sig
  type min_size_t = Min_size.min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf 
  val max_leaf_size : int
  val max_node_keys : int
  val min_leaf_size : int
  val min_node_keys : int
end

module type KEY_VALUE_TYPES = sig
  type key
  type value_t
  val key_ord : key -> key -> int
  val equal_value : value_t -> value_t -> bool (* only for wf checking *)
end

module Make = functor (C:CONSTANTS) -> functor (KV:KEY_VALUE_TYPES) -> struct

  module Constants = C
  module Key_value_types = KV

  type key = KV.key
  type value_t = KV.value_t

  let int_to_nat x = x |>Big_int.big_int_of_int|>Arith.nat_of_integer
  let int_to_int x = x |>Big_int.big_int_of_int|>(fun x -> Arith.Int_of_integer x)

  module Isa_c : Our.Constants_t = struct
    type min_size_t = Min_size.min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf 
    let max_leaf_size = C.max_leaf_size|>int_to_nat
    let max_node_keys = C.max_node_keys|>int_to_nat
    let min_leaf_size = C.min_leaf_size|>int_to_nat
    let min_node_keys = C.min_node_keys|>int_to_nat
  end

  module Isa_kv : Our.Key_value_types_t 
    with type key = KV.key and type value_t = KV.value_t 
  = struct
    type key = KV.key
    let key_ord k1 k2 = KV.key_ord k1 k2|>int_to_int
    let equal_keya k1 k2 = KV.key_ord k1 k2 = 0
    let equal_key = {HOL.equal = equal_keya}
    type value_t = KV.value_t
    let equal_value_ta = KV.equal_value
    let equal_value_t = {HOL.equal = equal_value_ta}
  end

  module M = Our.Make(Isa_c)(Isa_kv)
  
  type t = M.Tree.tree

  open M

  let empty : t = Tree.(Leaf[])

  module Find = struct
    (* FIXME wrap in constructor to get nice type? *)
    type t = (Tree.tree, unit) Tree_stack.core_t_ext *
          ((Key_value_types.key list * Tree.tree list), unit)
            Tree_stack.core_t_ext list
    let mk : key -> M.Tree.tree -> t = fun k0 t -> Find_tree_stack.mk_fts_state k0 t
    let step : t -> t option = Find_tree_stack.step_fts
    let dest = Find_tree_stack.dest_fts_state
  end

  module Insert = struct
    type t = Insert_tree_stack.its_state_t
    let mk : key -> value_t -> M.Tree.tree -> t = 
      fun k v t -> Insert_tree_stack.mk_its_state k v t
    let step : t -> t option = Insert_tree_stack.step_its
    let dest = Insert_tree_stack.dest_its_state
  end

  module Delete = struct
    type t = Delete_tree_stack.dts_state_t
    let mk : key -> M.Tree.tree -> t = 
      fun k t -> Delete_tree_stack.mk_dts_state k t
    let step : t -> t option = Delete_tree_stack.step_dts
                                 

  end

end
