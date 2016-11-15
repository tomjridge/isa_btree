let dest_Some = function (Some x) -> x | _ -> failwith "dest_Some"

let option_map f = function Some x -> Some(f x) | _ -> None

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
  type key [@@deriving yojson]
  type value_t [@@deriving yojson]
  val key_ord : key -> key -> int
  val equal_value : value_t -> value_t -> bool (* only for wf checking *)
end

module Make = functor (C:CONSTANTS) -> functor (KV:KEY_VALUE_TYPES) -> struct

  module Constants = C
  module Key_value_types = KV

  type key = KV.key
  type value_t = KV.value_t

  let int_to_nat x = Gen_isa.(x |>Big_int.big_int_of_int|>Arith.nat_of_integer)
  let int_to_int x = Gen_isa.(x |>Big_int.big_int_of_int|>(fun x -> Arith.Int_of_integer x))

  let key_eq k1 k2 = KV.key_ord k1 k2 = 0

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
    include KV
(*    type key = KV.key *)
    let key_ord k1 k2 = KV.key_ord k1 k2|>int_to_int
    let equal_keya k1 k2 = KV.key_ord k1 k2 = 0
    let equal_key = Gen_isa.{HOL.equal = equal_keya}
(*    type value_t = KV.value_t *)
    let equal_value_ta = KV.equal_value
    let equal_value_t = Gen_isa.{HOL.equal = equal_value_ta}
  end

  module M = Our.Make(Isa_c)(Isa_kv)
  
  type t = M.Tree.tree
  type t0 = t (* so we can refer to it without shadowing *)

  open M

  let empty : t = Tree.(Leaf[])

  let tree_to_leaves : t -> (key * value_t) list list = Tree.tree_to_leaves

  module Find = struct
    (* FIXME wrap in constructor to get nice type? *)
    type t = Find_tree_stack.fts_state_t

    let last_state : t option ref = ref None   
    let last_trans : (t*t option) option ref = ref None
    let check_state s = (
      last_state:=Some(s);
      assert (Find_tree_stack.wellformed_fts s);
    )
    let check_trans s s' = (
      last_trans:=Some(s,s');
      check_state s;
      match s' with
      None -> ()
      | Some t -> (
          check_state t;
          assert (Find_tree_stack.wf_fts_trans s t))
    )

    let mk : key -> M.Tree.tree -> t = fun k0 t -> Find_tree_stack.mk_fts_state k0 t

    let step : t -> t option = Find_tree_stack.step_fts

    let dest s = 
      s|>Find_tree_stack.dest_fts_state|>fst|>Tree_stack.f_t |>
      (fun foc -> 
         match foc with
           M.Tree.Leaf kvs -> Some(kvs)
         | _ -> None)

    let rec find : key -> t0 -> value_t option = (
      fun k t ->
        let s = ref (mk k t) in
        let _ = check_state !s in
        let s' = ref(Some(!s)) in
        let _ = 
          while(!s'<>None) do
            s := !s'|>dest_Some;
            s' := step !s;
            check_trans !s !s'
          done
        in
        (* !s' is None, so s holds the result *)
        let kvs : (key * value_t) list = !s|>dest|>dest_Some in
        let kv = 
          try
            Some(kvs|>List.find (function (x,y) -> key_eq x k))
          with Not_found -> None
        in
        kv|>option_map snd)

  end

  module Insert = struct
    type t = Insert_tree_stack.its_state_t

    let last_state : t option ref = ref None   
    let last_trans : (t*t option) option ref = ref None
    let check_state s = (
      last_state:=Some(s);
      assert (Insert_tree_stack.wellformed_its_state s)
    )
    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      match y with
      None -> ()
      | Some y' -> (
          check_state y';
          assert (Insert_tree_stack.wf_its_trans x y'))
    )

    let mk : key -> value_t -> M.Tree.tree -> t = 
      fun k v t -> Insert_tree_stack.mk_its_state k v t

    let step : t -> t option = Insert_tree_stack.step_its

    let dest = Insert_tree_stack.dest_its_state

    let rec insert : key -> value_t -> t0 -> t0 = (
      fun k v t ->
        let s = ref (mk k v t) in
        let _ = check_state !s in
        let s' = ref(Some(!s)) in
        let _ = 
          while(!s'<>None) do
            s := !s'|>dest_Some;
            s' := step !s;
            check_trans !s !s';
          done
        in
        (* !s' is None, so s holds the result *)
        !s|>dest|>dest_Some)
  end

  module Delete = struct

    type t = Delete_tree_stack.dts_state_t

    let last_state : t option ref = ref None   

    let last_trans : (t*t option) option ref = ref None

    let check_state s = (
      last_state:=Some(s);
      assert (Delete_tree_stack.wellformed_dts_state s)
    )

    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      match y with
      None -> ()
      | Some y' -> (
          check_state y';
          assert (Delete_tree_stack.wf_dts_trans x y'))
    )

    let mk : key -> M.Tree.tree -> t = 
      fun k t -> Delete_tree_stack.mk_dts_state k t

    let step : t -> t option = Delete_tree_stack.step_dts

    let dest = Delete_tree_stack.dest_dts_state

    let rec delete : key -> t0 -> t0 = (
      fun k t ->
        let s = ref (mk k t) in
        let _ = check_state !s in
        let s' = ref(Some(!s)) in
        let _ = 
          while(!s'<>None) do
            s := !s'|>dest_Some;
            s' := step !s;
            check_trans !s !s';
          done
        in
        (* !s' is None, so s holds the result *)
        !s|>dest|>dest_Some)
  end

end
