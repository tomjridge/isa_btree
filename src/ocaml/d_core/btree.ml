open Our



(* misc ---------------------------------------- *)

let dest_Some = function (Some x) -> x | _ -> failwith "dest_Some"

let option_map f = function Some x -> Some(f x) | _ -> None

let rec iter_step (f:'s -> 's option) (x:'s) = (
  let s' = f x in
  match s' with
  | None -> x
  | Some x' -> iter_step f x')


(* isa translations ---------------------------------------- *)

module X = struct

  let int_to_nat x = Gen_isa.(x |>Big_int.big_int_of_int|>Arith.nat_of_integer)
  let int_to_int x = Gen_isa.(x |>Big_int.big_int_of_int|>(fun x -> Arith.Int_of_integer x))

end



(* simplified structs ---------------------------------------- *)


module type KEY_VALUE_TYPES = Btree_api.KEY_VALUE

module type CONSTANTS = Btree_api.CONSTANTS

module type STORE = Btree_api.STORE


(* construct non-simple versions suitable for isa -------------------------- *)

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

module Mk_st = functor (ST:STORE) -> struct

  module ST = ST

  module T = struct
    type page = ST.page
    type store = ST.store
    type page_ref = ST.page_ref[@@deriving yojson]
    
    open Our
    let to_our_monad : 'a ST.M.m -> ('a,store) Our.Monad.m_t = (
      fun x -> Our.Monad.M(
          fun s -> (
              x |> ST.M.run s |> (fun r -> 
                  match r with
                  (s',Ok(z)) -> (s',Our.Util.Ok(z))
                  | (s',Error e) -> (s',Our.Util.Error (Our.Util.String_error e)))
        )
    ))

    let free : page_ref list -> (unit, store) Monad.m_t = (fun ps ->
        ST.free ps |> to_our_monad)

    let alloc : page -> (page_ref, store) Monad.m_t = (fun p ->
        ST.alloc p |> to_our_monad)

    let dest_Store : store -> page_ref -> page = ST.dest_Store

    let page_ref_to_page : page_ref -> (page, store) Monad.m_t = (fun r ->
        ST.page_ref_to_page r |> to_our_monad)
  end

  include T

end


(* main functor ---------------------------------------- *)

(* this is the most general interface to the btree routines *)

module Main = struct

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
          Leaf_frame of (key * value) list[@@deriving yojson]

      val frame_to_page : pframe -> page
      val page_to_frame : page -> pframe
    end

  end


  module Make = functor (S:S) -> struct


    (* set up to call our.make ---------------------------------------- *)

    module S = S

    (* don't want these infecting the namespace *)
    module Btree_private = struct

      module C = Mk_c(S.C)

      module KV = Mk_kv(S.KV)

      module ST = Mk_st(S.ST)

      module Frame_types = struct
        module Store = ST
        module Key_value_types = struct 
          include KV
          type value_t = value
          let value_t_of_yojson = KV.value_of_yojson
          let value_t_to_yojson = KV.value_to_yojson
        end
        include S.FT

        (* implement dest_Store *)
      end

    end

    (* use our.make functor ---------------------------------------- *)

    module Our' = Our.Make(Btree_private.C)(Btree_private.Frame_types)

    open Our'

  (*
  module Tree = Our'.Tree
  module Store = Our'.Frame_types.Store
  module Frame = Our'.Frame
     *)

    type t = Tree.tree
    type t0 = t (* so we can refer to it without shadowing *)

    (* open M *)

    let empty : t = Tree.(Leaf[])

    (* let tree_to_leaves : t -> (key * value_t) list list = Tree.tree_to_leaves *)

    module Find = struct

      module Find = Our'.Find

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
        Test.test (fun _ -> 
          assert (Find.wellformed_find_state s.store s.tree s.fs));            
      )

      let check_trans s s' = (
        last_trans:=Some(s,s');
        check_state s;
        check_state s'
      )

      let mk : Key_value_types.key -> Store.page_ref -> Store.store -> t = 
        fun k0 r s -> {tree=Frame.r_to_t s r; store=s; fs=Find.mk_find_state k0 r}

      let step : t -> t = (fun x ->
          let (s',Our.Util.Ok fs') = (Find.find_step x.fs |> Monad.dest_M) x.store in
          {x with fs=fs'})


      (* for testing *)
      let find_1 : Store.store -> Key_value_types.key -> Store.page_ref -> t = (
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

      let find : Store.store -> Key_value_types.key -> Store.page_ref -> Key_value_types.value_t option = (
        fun st k r ->
          let s' = find_1 st k r in
          (* s' is finished *)
          let (r0,(k,(r,(kvs,stk)))) = (s').fs|>Find.dest_f_finished|>dest_Some in
          let kv = 
            try
              Some(kvs|>List.find (function (x,y) -> Key_value.key_eq x k))
            with Not_found -> None
          in
          kv|>option_map snd)

    end


    module Insert = struct

      module Insert = Our'.Insert

      type t = {
        t: Tree.tree;
        k:Key_value_types.key;
        v:Key_value_types.value_t;
        store: Store.store;
        is: Insert.i_state_t
      }

      let last_state : t option ref = ref None   

      let last_trans : (t*t) option ref = ref None

      let check_state s = (
        last_state:=Some(s);
        Test.test (fun _ ->
            assert (Insert.wellformed_insert_state s.t s.k s.v s.store s.is));
      )

      let check_trans x y = (
        last_trans:=Some(x,y);
        check_state x;
        check_state y
      )

      let mk : Store.store -> Key_value_types.key -> Key_value_types.value_t -> Store.page_ref -> t = 
        fun s k v r ->{t=(Frame.r_to_t s r);k;v;store=s;is=(Insert.mk_insert_state k v r)}

      let step : t -> t = (fun x ->
          let (s',Our.Util.Ok is') = (Insert.insert_step x.is|>Monad.dest_M) x.store in
          {x with store=s';is=is'})

      let dest = Insert.dest_i_finished

      let insert : Key_value_types.key -> Key_value_types.value_t -> Store.page_ref -> Store.store -> (Store.store * Store.page_ref) = (
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

      module Insert_many = Our'.Insert_many

      type t = {
        t: Tree.tree;
        k:Key_value_types.key;
        v:Key_value_types.value_t;
        store: Store.store;
        is: Insert_many.i_state_t
      }

      let last_state : t option ref = ref None   

      let last_trans : (t*t) option ref = ref None

      let check_state s = (
        last_state:=Some(s);
        Test.test (fun _ -> 
            assert (true));
        ()
      )

      let check_trans x y = (
        last_trans:=Some(x,y);
        check_state x;
        check_state y
      )

      type kvs = (Key_value_types.key * Key_value_types.value_t) list

      let mk : Store.store -> Key_value_types.key -> Key_value_types.value_t -> kvs -> Store.page_ref -> t = 
        fun s k v kvs r ->{t=(Frame.r_to_t s r);k;v;store=s;is=(Insert_many.mk_insert_state k v kvs r)}

      let step : t -> t = (fun x ->
          let (s',Our.Util.Ok is') = (Insert_many.insert_step x.is|>Monad.dest_M) x.store in
          {x with store=s';is=is'})

      let dest = Insert_many.dest_i_finished

      let insert : Key_value_types.key -> Key_value_types.value_t -> kvs -> Store.page_ref -> Store.store -> (Store.store * (Store.page_ref * kvs)) = (
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

      module Delete = Our'.Delete

      type t = {
        t:Tree.tree;
        k:Key_value_types.key;
        store:Store.store;
        ds:Delete.d_state
      }

      let last_state : t option ref = ref None   

      let last_trans : (t*t) option ref = ref None

      let check_state s = (
        last_state:=Some(s);
        Test.test (fun _ -> 
          assert (Delete.wellformed_delete_state s.t s.k s.store s.ds));
        ()
      )

      let check_trans x y = (
        last_trans:=Some(x,y);
        check_state x;
        check_state y
      )

      let mk : Store.store -> Key_value_types.key -> Store.page_ref -> t = 
        fun s k r -> {
            t=(Frame.r_to_t s r);
            k;
            store=s;
            ds=(Delete.mk_delete_state k r)
          }

      let step : t -> t = (fun x ->
          let (s',Our.Util.Ok ds') = (Delete.delete_step x.ds|>Monad.dest_M) x.store in
          {x with store=s';ds=ds'})

      let dest = Delete.dest_d_finished

      let delete : Key_value_types.key -> Store.page_ref -> Store.store -> (Store.store * Store.page_ref) = (
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
          | D_up (f,(stk,r)) -> `D_up(from_store s f,stk|>List.map (Our'.Frame.r_frame_to_t_frame s))
          | D_finished(r) -> `D_finished(r|>Frame.r_to_t s)
        )

    end

  end


end (* Main *)

