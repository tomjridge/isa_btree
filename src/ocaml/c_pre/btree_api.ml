(* various interfaces ---------------------------------------- *)

(* store passing with error *)

module Lens = struct

  (* 'a splits as (b,c) *)
  type ('l,'s,'r) t = {  (* large, small, rest *)
    from: 'l -> ('s * 'r);
    to_: ('s * 'r -> 'l)
  }

end

module State_monad : sig
  type ('a,'s) m = 's -> ('s * 'a)
  val return: 'a -> ('a,'s) m
  val bind: ('a -> ('b,'s) m) -> ('a,'s) m -> ('b,'s) m
  val run: 's -> ('a,'s) m -> ('s * 'a)
end = struct
  type ('a,'s) m = 's -> ('s * 'a)
  let return: 'a -> ('a,'s) m = fun x -> fun s -> (s,x)
  let bind: ('a -> ('b,'s) m) -> ('a,'s) m -> ('b,'s) m = 
    fun f m -> fun s ->
      m s |> (fun (s',a) -> f a s') 
  let run: 's -> ('a,'s) m -> 's * 'a = fun s -> fun m -> m s
end

module S_m = State_monad

module State_error_monad : sig
  type ('a,'s) m = 's -> ('s * ('a,string) result)
  val return: 'a -> ('a,'s) m
  val bind: ('a -> ('b,'s) m) -> ('a,'s) m -> ('b,'s) m
  val fmap: ('a -> 'b) -> ('a,'s) m -> ('b,'s) m
  val run: 's -> ('a,'s) m -> 's * ('a,string) result
  val unsafe_run: 's ref -> ('a,'s) m -> 'a (* mainly for testing *)
  val with_lens: ('l,'s,'r) Lens.t -> ('a,'s) m -> ('a,'l) m
(*  val get: ('s,'s) m  *)
  val run_list: 's -> (unit,'s) m list -> 's * (unit,string) result
  val err: string -> ('a,'s) m
  val safely: string -> ('a,'s) m -> ('a,'s) m
end = struct
  type ('a,'s) m = 's -> ('s * ('a,string) result)

  let return: 'a -> ('a,'s) m = (fun x -> (fun s -> (s,Ok x)))

  let bind: ('a -> ('b,'s) m) -> ('a,'s) m -> ('b,'s) m = (
    fun f x -> (
        fun s -> match x s with
          | (s',Error e) -> (s',Error e)
          | (s',Ok y) -> (f y s')
      ))

  let err e = (fun s -> (s,Error e))


  let fmap: ('a -> 'b) -> ('a,'s) m -> ('b,'s) m = (
    fun f -> fun m -> fun s ->
      m s |> 
      (fun (s',r) -> (s',
                      match r with
                      | Ok x-> Ok (f x)
                      | Error e -> Error e)))
      
  let run: 's -> ('a,'s) m -> 's * ('a,string) result = (fun s f -> f s)

  let unsafe_run s m = m |> run !s |> (fun (s',res) -> 
      s:=s'; match res with Ok x -> x | Error e -> failwith (__LOC__ ^ e))

  (* lifting to another state monad *)
  let with_lens: ('l,'s,'r) Lens.t -> ('a,'s) m -> ('a,'t) m = (fun l m ->
      fun t -> 
        l.from t |> 
        (fun (s,r) -> 
           run s m 
           |> (fun (s',res) -> (l.to_ (s',r),res))))

(*
  let get: ('s,'s) m = (fun s -> (s,Ok s)) 
*)

  let rec run_list s xs = (
    match xs with
    | [] -> (s,Ok())
    | x::xs' -> (
        x|>run s|>(fun (s',res) ->
            match res with
            | Ok () -> (run_list s' xs')
            | Error e -> (s',Error e))
      ))

  let safely = (
    fun msg m ->
      fun s -> 
        try m s 
        with e -> (s,Error (msg ^ (Printexc.to_string e))))
end

(* short name *)
module Sem = State_error_monad



module type KEY_VALUE = sig
  type key [@@deriving yojson]
  type value [@@deriving yojson]
  val key_ord : key -> key -> int
  val equal_value : value -> value -> bool (* only for wf checking *)
end

module type CONSTANTS = sig
  val max_leaf_size : int
  val max_node_keys : int
  val min_leaf_size : int
  val min_node_keys : int
end

(* we require that the store makes errors explicit so we can
   explicitly handle them (ie maintain invariants); if we don't have
   any resources, then an exception just unwinds the stack (so is
   safe); otherwise we need to use exceptions very carefully, in which
   case we might as well be explicit *)
module type STORE = sig
  type page
  type store
  type page_ref [@@deriving yojson]

  type 'a m = ('a,store) Sem.m

  val free: page_ref list -> unit m
  val alloc: page -> page_ref m
  val dest_Store: store -> page_ref -> page
  val page_ref_to_page: page_ref -> page m
end


(* map-like interfaces ======================================== *)

(* raw map ---------------------------------------- *)

(* like a map, but pointers are explicit *)
module type RAW_MAP = sig
  module KV : KEY_VALUE
  module ST : STORE
  type ref_t = ST.page_ref

  type 'a m = ('a,ST.store * ref_t) Sem.m

  open KV
  val empty: unit -> (ref_t,ST.store) Sem.m
  val insert: key -> value -> unit m
  val insert_many: key -> value -> (key*value) list -> unit m
  val find: key -> value option m
  val delete: key -> unit m

end



(* leaf stream ---------------------------------------- *)

(* this is a useful operation to support, but not needed always *)
module type LEAF_STREAM = sig
  module ST : STORE
  module KV : KEY_VALUE
  open KV

  type t  (* pointer to somewhere in btree *)
  type 'a m = ('a,ST.store * t) Sem.m

  val mk: ST.page_ref -> (t,ST.store) Sem.m
  val step: unit -> bool m  (* true if we have stepped *)
  val get_kvs: unit -> (key*value) list m
end


(* simple interface ---------------------------------------- *)

(* see Btree_simple *)

module Pickle_params = struct
  open Pickle
  type ('k,'v) t = {
    p_k: 'k -> P.m;
    u_k: 'k U.m;
    k_len: int;
    p_v: 'v -> P.m;
    u_v: 'v U.m;
    v_len: int      
  }
end  

module Simple = struct
  type page_ref = int[@@deriving yojson]
  type page = string (* ie immutable bytes *)

  module type STORE = sig (* FIXME STORE *)
    include STORE with type page_ref = page_ref
                   and type page = page 
    val page_size : int (* bytes per page; needed to compute constants *)
  end

  module type S = sig
    module KV: KEY_VALUE
    module ST: STORE
    open KV
    val pp: (key,value) Pickle_params.t 
  end (* S *)
end


(* block device ---------------------------------------- *)

(* what is typically provided by the file system; used to provide the
   store interface *)
module type BLOCK_DEVICE = sig
  type t
  type r
  type blk
  type 'a m = ('a,t) Sem.m

  val block_size: int
  val string_to_blk: string -> (blk,string) result
  val read: r -> blk m
  val write: r -> blk -> unit m
  val sync: unit -> unit m  
end







(* old ---------------------------------------- *)

(* type 'a itself = 'a *)


(*
module Step : sig

end = struct

  type ('a,'t,'g) m = Core_kernel.

(* Suc of ('g -> ('a,'t,'g) m) | Finished of ('a,'t,'g) *)

  let is_finished = (function
      | Suc _ -> false
      | _ -> true)

  let step: 'g -> ('a,'t,'g) m -> ('a,'t,'g) m = (function
      | Suc x -> x()
      | _ -> failwith "Step.step")

  let rec run: 'g -> ('a,'t,'g) m -> ('a,'t,'g) = (function
      | Finished x -> x
      | Suc x -> run (step x))

end
*)

(* from a runnable we can concoct a store_monad? *)
(*
module type MONAD = sig
  type 'a m
  val return: 'a -> 'a m
  val bind: ('a -> 'b m) -> 'a m -> 'b m
end
*)
(*
module type STORE_MONAD = sig
  module Runnable : RUNNABLE
  include MONAD with type 'a m = 'a Runnable.m 
end
*)


(* as RAW_MAP, but throw exceptions *)
(*
module type MAP_WITH_EXCEPTIONS = sig
  module KV : KEY_VALUE
  module ST : STORE
  type ref_t = ST.page_ref

  type 'a m = ('a,ST.store * ref_t) State_monad.m

  open KV
  (* empty: not unit m - we don't have a ref_t *)
  val empty: (ref_t,ST.store) Sem.m
  val insert: key -> value -> unit m
  val insert_many: key -> value -> (key*value) list -> unit m
  val find: key -> value option m
  val delete: key -> unit m
end
*)



(* imperative map ---------------------------------------- *)

(*
type ('key,'value) imperative_map_t = { 
  insert: 'key -> 'value -> unit;
  insert_many: 'key -> 'value -> ('key*'value) list -> unit;
  find: 'key -> 'value option;
  delete: 'key -> unit;
}

(* as MAP_WITH_EXCEPTIONS, but with mutable state, and btree_ref is
   encapsulated in an object *)
module type IMPERATIVE_MAP = sig
  module ST : STORE
  module KV : KEY_VALUE
  open KV
  val mk: ST.store ref -> ST.page_ref ref -> (key,value) imperative_map_t
end
*)



(* imperative leaf stream ---------------------------------------- *)

(*
type ('key,'value) imperative_leaf_stream_t = {
  step: unit -> bool;
  get_kvs: unit -> ('key * 'value) list;
}

(* for debugging FIXME move *)
let all_kvs: ('key,'value) imperative_leaf_stream_t -> ('key*'value) list = (
  fun ops -> 
    let x = ref (ops.get_kvs()) in
    while(ops.step()) do
      x:=!x @ (ops.get_kvs());
    done;
    !x)

module type IMPERATIVE_LEAF_STREAM = sig
  module ST : STORE
  module KV : KEY_VALUE
  module LS : LEAF_STREAM
  open KV
  val mk:ST.store -> ST.page_ref -> 
    (ST.store * LS.t) ref * (key,value) imperative_leaf_stream_t
end
*)


(*
module type RUNNABLE = sig
  type 'a m
  type state
  val run: state -> 'a m -> (state * ('a,string) result) 
qend
*)

