(* map from string to int using Digest.t MD5 128bit hash of string *)

let failwith x = failwith ("ext_string_int: "^x)

open Ext_block_device

(* assumptions ---------------------------------------- *)

let block_size = Block.size

let int_size = 4 (* bytes *)

let digest_size = 128/8 (* bytes *)

let key_size = digest_size


(* Btree.Simple.Make() ------------------------------------------- *)

open Btree.Simple  

module Make = functor (ST:STORE) -> struct

  module S = struct 

    module KV = struct

      (* we map string to int using hash *)
      type pre_key = string

      type digest_t = string[@@deriving yojson]

      type key = digest_t[@@deriving yojson] (* 16 char strings *)

      type value_t = int[@@deriving yojson]

      let key_ord = Digest.compare

      let equal_value x y = (x:int) = y

    end (* KV *)

    module KV_ = (KV : Btree.KEY_VALUE_TYPES)

    module ST=ST

    module Sz : Sz_t = struct
      let b : int = block_size
      let k : int = 128 / 32
      let v : int = 1
      let r : int = 1
    end

    module X = struct
      open Btree_util
      open M_int32s
      let i : int cnv = X.i
      let k = X.s
      let v = X.i
      let r = X.i
    end

  end (* S *)

  module S_ = (S: Btree.Simple.S)

  module Simple' = Btree.Simple.Make(S)

end
