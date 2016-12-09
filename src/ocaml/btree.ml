open Our

(* debug config  ---------------------------------------- *)

type config = {
  check_wellformedness: bool
}


let config = { check_wellformedness=false }


(* misc ---------------------------------------- *)

let dest_Some = function (Some x) -> x | _ -> failwith "dest_Some"

let option_map f = function Some x -> Some(f x) | _ -> None

module X = struct

  let int_to_nat x = Gen_isa.(x |>Big_int.big_int_of_int|>Arith.nat_of_integer)
  let int_to_int x = Gen_isa.(x |>Big_int.big_int_of_int|>(fun x -> Arith.Int_of_integer x))

end


(* simplified structs ---------------------------------------- *)


module type KEY_VALUE_TYPES = sig
  type key [@@deriving yojson]
  type value_t [@@deriving yojson]
  val key_ord : key -> key -> int
  val equal_value : value_t -> value_t -> bool (* only for wf checking *)
end

module type CONSTANTS = sig
  val max_leaf_size : int
  val max_node_keys : int
  val min_leaf_size : int
  val min_node_keys : int
end

module type STORE = sig
  type page 
  type page_ref [@@deriving yojson]
  type store 
  type store_error
  val alloc : page -> store -> store * (page_ref, store_error) Util.rresult
  val dest_Store : store -> page_ref -> page (* FIXME remove *)
  val page_ref_to_page :
    page_ref -> store -> store * (page, store_error) Util.rresult
  val free : page_ref list -> store -> store * (unit, store_error) Util.rresult
end


module type S = sig

  module C : CONSTANTS

  module KV: KEY_VALUE_TYPES
  
  module ST: STORE

  (* this module's types depend on the previous modules *)
  module FT : sig
    open KV
    open ST
    type pframe =  
        Node_frame of (key list * page_ref list) |
        Leaf_frame of (key * value_t) list[@@deriving yojson]

    val frame_to_page : pframe -> page
    val page_to_frame : page -> pframe
  end

end


module Mk_kv = functor (KV:KEY_VALUE_TYPES) -> struct

  open X

  include KV

  let key_eq k1 k2 = KV.key_ord k1 k2 = 0
  let key_ord k1 k2 = KV.key_ord k1 k2|>int_to_int
  let equal_keya k1 k2 = KV.key_ord k1 k2 = 0
  let equal_key = Gen_isa.{HOL.equal = equal_keya}
  let equal_value_ta = KV.equal_value
  let equal_value_t = Gen_isa.{HOL.equal = equal_value_ta}

end

module Mk_c = functor (C:CONSTANTS) -> struct
  type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf 
  let max_leaf_size = C.max_leaf_size |> X.int_to_nat
  let max_node_keys  = C.max_node_keys|>X.int_to_nat
  let min_leaf_size = C.min_leaf_size|>X.int_to_nat
  let min_node_keys = C.min_node_keys|>X.int_to_nat
end


(* main functor ---------------------------------------- *)

module Make = functor (S:S) -> struct


  (* set up to call our.make ---------------------------------------- *)

  module S = S

  module C = Mk_c(S.C)

  module KV = Mk_kv(S.KV)

  module Frame_types = struct
    module Store = S.ST
    module Key_value_types = KV
    include S.FT
  end


  (* use our.make functor ---------------------------------------- *)

  module M = Our.Make(C)(Frame_types)
  
  module Tree = M.Tree
  module Store = M.Frame_types.Store
  module Frame = M.Frame

  type t = M.Tree.tree
  type t0 = t (* so we can refer to it without shadowing *)

  (* open M *)

  let empty : t = Tree.(Leaf[])

  (* let tree_to_leaves : t -> (key * value_t) list list = Tree.tree_to_leaves *)

  module Find = struct

    module Find = M.Find

    (* FIXME wrap in constructor to get nice type? *)
    type t = {
      tree: Tree.tree;
      store: Store.store;
      fs: Find.find_state
    }
    
    let dest_finished s' = (s').fs|>Find.dest_f_finished|>dest_Some

    let last_state : t option ref = ref None   

    let last_trans : (t*t) option ref = ref None

    let check_state s = (
      last_state:=Some(s);
      if (config.check_wellformedness) then
        assert (Find.wellformed_find_state s.store s.tree s.fs)
      else ();
    )

    let check_trans s s' = (
      last_trans:=Some(s,s');
      check_state s;
      check_state s'
    )

    let mk : KV.key -> Store.page_ref -> Store.store -> t = 
      fun k0 r s -> {tree=Frame.r_to_t s r; store=s; fs=Find.mk_find_state k0 r}

    let step : t -> t = (fun x ->
      let (s',Our.Util.Ok fs') = Find.find_step x.fs x.store in
      {x with fs=fs'})


    (* for testing *)
    let find_1 : Store.store -> KV.key -> Store.page_ref -> t = (
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
        !s'
    )

    let find : Store.store -> KV.key -> Store.page_ref -> KV.value_t option = (
      fun st k r ->
        let s' = find_1 st k r in
        (* s' is finished *)
        let (r0,(k,(r,(kvs,stk)))) = (s').fs|>Find.dest_f_finished|>dest_Some in
        let kv = 
          try
            Some(kvs|>List.find (function (x,y) -> KV.key_eq x k))
          with Not_found -> None
        in
        kv|>option_map snd)

  end


  module Insert = struct

    module Insert = M.Insert

    type t = {
      t: Tree.tree;
      k:KV.key;
      v:KV.value_t;
      store: Store.store;
      is: Insert.i_state_t
    }

    let last_state : t option ref = ref None   

    let last_trans : (t*t) option ref = ref None

    let check_state s = (
      last_state:=Some(s);
      if (config.check_wellformedness) then
        assert (Insert.wellformed_insert_state s.t s.k s.v s.store s.is)
      else ();
    )

    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      check_state y
    )

    let mk : Store.store -> KV.key -> KV.value_t -> Store.page_ref -> t = 
      fun s k v r ->{t=(Frame.r_to_t s r);k;v;store=s;is=(Insert.mk_insert_state k v r)}

    let step : t -> t = (fun x ->
        let (s',Our.Util.Ok is') = Insert.insert_step x.is x.store in
        {x with store=s';is=is'})

    let dest = Insert.dest_i_finished

    let insert : KV.key -> KV.value_t -> Store.page_ref -> Store.store -> (Store.store * Store.page_ref) = (
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


  module Insert_many = struct

    module Insert_many = M.Insert_many

    type t = {
      t: Tree.tree;
      k:KV.key;
      v:KV.value_t;
      store: Store.store;
      is: Insert_many.i_state_t
    }

    let last_state : t option ref = ref None   

    let last_trans : (t*t) option ref = ref None

    let check_state s = (
      last_state:=Some(s);
      if (config.check_wellformedness) then
        assert (true)
      else ();
    )

    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      check_state y
    )

    type kvs = (KV.key * KV.value_t) list

    let mk : Store.store -> KV.key -> KV.value_t -> kvs -> Store.page_ref -> t = 
      fun s k v kvs r ->{t=(Frame.r_to_t s r);k;v;store=s;is=(Insert_many.mk_insert_state k v kvs r)}

    let step : t -> t = (fun x ->
        let (s',Our.Util.Ok is') = Insert_many.insert_step x.is x.store in
        {x with store=s';is=is'})

    let dest = Insert_many.dest_i_finished

    let insert : KV.key -> KV.value_t -> kvs -> Store.page_ref -> Store.store -> (Store.store * (Store.page_ref * kvs)) = (
      fun k v kvs r store ->
        let s = ref (mk store k v kvs r) in
        let _ = check_state !s in
        let s' = ref(!s) in
        let _ = 
          while((!s').is|>dest = None) do
            s := !s';
            s' := step !s;
            check_trans !s !s';
          done
        in        
        let (r,kvs') = (!s').is|>dest|>dest_Some in
        ((!s').store,(r,kvs')))

  end



  module Delete = struct

    module Delete = M.Delete

    type t = {
      t:Tree.tree;
      k:KV.key;
      store:Store.store;
      ds:Delete.d_state
    }

    let last_state : t option ref = ref None   

    let last_trans : (t*t) option ref = ref None

    let check_state s = (
      last_state:=Some(s);
      if (config.check_wellformedness) then
        assert (Delete.wellformed_delete_state s.t s.k s.store s.ds)
      else ()
    )

    let check_trans x y = (
      last_trans:=Some(x,y);
      check_state x;
      check_state y
    )

    let mk : Store.store -> KV.key -> Store.page_ref -> t = 
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

    let delete : KV.key -> Store.page_ref -> Store.store -> (Store.store * Store.page_ref) = (
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


    (* need some pretty *)
    let from_store s t = Delete.(
      let from_store s f = (
        match f with
        D_small_leaf kvs -> `D_small_leaf kvs
        | D_small_node(ks,rs) -> `D_small_node(ks,rs|>List.map (Frame.r_to_t s))
        | D_updated_subtree(r) -> `D_updated_subtree(r|>Frame.r_to_t s)
      )
      in
      match t.ds with
      | D_down (fs,r) -> `D_down (* FIXME fs *)
      | D_up (f,(stk,r)) -> `D_up(from_store s f,stk|>List.map (M.Monad2.r_frame_to_t_frame s))
      | D_finished(r) -> `D_finished(r|>Frame.r_to_t s)
    )

  end

end



(*


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



  (* stores, pages and frames *)

  module Frames_etc = struct

    module Pre_store = struct
      type page_ref = int[@@deriving yojson]
    end

    module Key_value_types = Isa_kv

    module Pre_frame = struct 

      type pframe =  
          Node_frame of (Key_value_types.key list * Pre_store.page_ref list) |
          Leaf_frame of (Key_value_types.key * Key_value_types.value_t) list[@@deriving yojson]

      type page = pframe

      let frame_to_page : pframe -> page = fun x -> x
      let page_to_frame : page -> pframe = fun x -> x
    end

    module Map_int = Map.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)

    module Store_1 = struct
      include Pre_store
      type page = Pre_frame.pframe
      type store = {free:int; m:page Map_int.t}
      type store_error = unit
      let dest_Store : store -> page_ref -> page = (fun s r -> Map_int.find r s.m)

      let page_ref_to_page r s = (s,Our.Util.Ok(Map_int.find r s.m))
      let alloc p s = (
        let f = s.free in
        ({free=(f+1);m=Map_int.add f p s.m}),Our.Util.Ok(f))

      (* for empty store, we want an empty leaf at page 0 *)
      let empty_store () = (
        {free=1;m=Map_int.empty |> Map_int.add 0 (Pre_frame.Leaf_frame[])},
        0)

    end

    module Frame_types : Our.Frame_types_t with module Store=Store_1 and module Key_value_types = Isa_kv = struct
      module Store = Store_1
      module Key_value_types = Isa_kv
      include Pre_frame



*)
