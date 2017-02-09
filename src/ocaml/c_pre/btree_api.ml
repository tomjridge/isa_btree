(* various interfaces ---------------------------------------- *)

module type MONAD = sig

  type 'a m

  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m

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

module type STORE = Our.Store_t


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

  module type ST_t = sig 

    include STORE with type page_ref = int 
                   and type page = string (* ie immutable bytes *)

    val page_size : int (* bytes per page *)

  end

  module type S = sig

    module KV: KEY_VALUE

    module ST: ST_t

    open KV
    val pp: (key,value) Pickle_params.t 

  end (* S *)

  module type T = MAP  (* output type of Simple.Make(S) *)

end


(* block device ---------------------------------------- *)

(* what is typically provided by the file system; used to provide the store interface *)
module type BLOCK_DEVICE = sig

  type t
  type r
  type blk

  module M : MONAD

  val read: r -> blk M.m
  val write: r -> blk -> unit M.m
  val sync: unit M.m

end
