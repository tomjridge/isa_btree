(* various interfaces ---------------------------------------- *)

module type MONAD = sig
  type 'a m
  val return: 'a -> 'a m
  val bind: ('a -> 'b m) -> 'a m -> 'b m
end

module type STORE_MONAD = sig
  include MONAD
  type store
  val run: store -> 'a m -> (store * ('a,string) result)
end


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

module type STORE = sig
  type page
  type store
  type page_ref [@@deriving yojson]
  module M : STORE_MONAD with type store = store
  val free : page_ref list -> unit M.m
  val alloc : page -> page_ref M.m
  val dest_Store : store -> page_ref -> page
  val page_ref_to_page : page_ref -> page M.m
end


module type MAP = sig
  module KV : KEY_VALUE
  module ST : STORE
  module M : MONAD
  open KV
  val insert: key -> value -> unit M.m
  val insert_many: (key*value) list -> unit M.m
  val find: key -> value option M.m
  val delete: key -> unit M.m
end



(* simple interface ---------------------------------------- *)

module Pickle_params = struct

  open Pickle

  type ('k,'v) t = {
    p_k: 'k -> unit P.m;
    u_k: 'k U.m;
    k_len: int;
    p_v: 'v -> unit P.m;
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

  module type T = MAP  (* output type of Simple.Make(S) *)
end


(* block device ---------------------------------------- *)

(* what is typically provided by the file system; used to provide the store interface *)
module type BLOCK_DEVICE = sig
  type t (* FIXME needed? *)
  type r
  type blk
  module M : MONAD
  val read: r -> blk M.m
  val write: r -> blk -> unit M.m
  val sync: unit M.m  (* FIXME needed in interface? *)
end
