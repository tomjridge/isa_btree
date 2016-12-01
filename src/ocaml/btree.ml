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
    type t = {
      tree: Tree.tree;
      store: Store.store;
      fs: Find.find_state
    }

    let last_state : t option ref = ref None   
    let last_trans : (t*t) option ref = ref None
    let check_state s = (
      last_state:=Some(s);
      assert (Find.wellformed_find_state s.store s.tree s.fs);
    )
    let check_trans s s' = (
      last_trans:=Some(s,s');
      check_state s;
      check_state s'
    )

    let mk : key -> Store.page_ref -> Store.store -> t = 
      fun k0 r s -> {tree=Frame.r_to_t s r; store=s; fs=Find.mk_find_state k0 r}

    let step : t -> t = (fun x ->
      let (s',Our.Util.Ok fs') = Find.find_step x.fs x.store in
      {x with fs=fs'})

(*
    let dest s = 
      s|>Find_tree_stack.dest_fts_state|>fst|>Tree_stack.f_t |>
      (fun foc -> 
         match foc with
           M.Tree.Leaf kvs -> Some(kvs)
         | _ -> None)
*)

    let rec find : Store.store -> key -> Store.page_ref -> value_t option = (
      fun st k r ->
        let s = ref (mk k r st) in
        let _ = check_state !s in
        let s' = s in
        let _ = 
          while((!s').fs|>Find.dest_f_finished = None) do
            s := !s';
            s' := step !s;
            check_trans !s !s'
          done
        in
        (* !s' is None, so s holds the result *)
        let (k,(r,(kvs,stk))) = (!s).fs|>Find.dest_f_finished|>dest_Some in
        let kv = 
          try
            Some(kvs|>List.find (function (x,y) -> key_eq x k))
          with Not_found -> None
        in
        kv|>option_map snd)

  end

  module Insert = struct
    type t = {
      t: Tree.tree;
      k:key;
      v:value_t;
      store: Store.store;
      is: Insert.i_state_t
    }

    let last_state : t option ref = ref None   
    let last_trans : (t*t) option ref = ref None
    let check_state s = (
      last_state:=Some(s);
      assert (Insert.wellformed_insert_state s.t s.k s.v s.store s.is)
    )
    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      check_state y
    )

    let mk : Store.store -> key -> value_t -> Store.page_ref -> t = 
      fun s k v r ->{t=(Frame.r_to_t s r);k;v;store=s;is=(Insert.mk_insert_state k v r)}

    let step : t -> t = (fun x ->
        let (s',Our.Util.Ok is') = Insert.insert_step x.is x.store in
        {x with store=s';is=is'})

    let dest = Insert.dest_i_finished

    let rec insert : key -> value_t -> Store.page_ref -> Store.store -> (Store.store * Store.page_ref) = (
      fun k v r store ->
        let s = ref (mk store k v r) in
        let _ = check_state !s in
        let s' = ref(!s) in
        let _ = 
          while((!s').is|>dest = None) do
            s := !s';
            s' := step !s;
            check_trans !s !s';
          done
        in        
        let r = (!s').is|>dest|>dest_Some in
        ((!s').store,r))
  end

  module Delete = struct

    type t = {
      t:Tree.tree;
      k:key;
      store:Store.store;
      ds:Delete.d_state
    }

    let last_state : t option ref = ref None   

    let last_trans : (t*t) option ref = ref None

    let check_state s = (
      last_state:=Some(s);
      assert (Delete.wellformed_delete_state s.t s.k s.store s.ds)
    )

    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      check_state y
    )

    let mk : Store.store -> key -> Store.page_ref -> t = 
      fun s k r -> {
          t=(Frame.r_to_t s r);
          k;
          store=s;
          ds=(Delete.mk_delete_state k r)
        }

    let step : t -> t = (fun x ->
        let (s',Our.Util.Ok ds') = Delete.delete_step x.ds x.store in
        {x with store=s';ds=ds'})

    let dest = Delete.dest_d_finished

    let rec delete : key -> Store.page_ref -> Store.store -> (Store.store * Store.page_ref) = (
      fun k r store ->
        let s = ref (mk store k r) in
        let _ = check_state !s in
        let s' = ref(!s) in
        let _ = 
          while((!s').ds|>dest = None) do
            s := !s';
            s' := step !s;
            check_trans !s !s';
          done
        in
        let r = (!s').ds|>dest|>dest_Some in
        (* !s' is None, so s holds the result *)
        ((!s').store,r))
  end

end
