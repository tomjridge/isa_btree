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

    module KV : Btree.KEY_VALUE_TYPES = struct

      (* we map string to int using hash *)
      type pre_key = string

      type digest_t = string[@@deriving yojson]

      type key = digest_t[@@deriving yojson] (* 16 char strings *)

      type value_t = int[@@deriving yojson]

      let key_ord = Digest.compare

      let equal_value x y = (x:int) = y

    end (* KV *)


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

  


  module S' = struct
    module C=C
    module KV=KV
    module ST=ST

    module FT = struct

      open KV
      open ST
      (* format: int node_or_leaf; int number of entries; entries *)

      type pframe =  
          Node_frame of (key list * page_ref list) |
          Leaf_frame of (key * value_t) list[@@deriving yojson]

      let frame_to_page' : pframe -> page = (
        fun p ->
          let is = (
            match p with
              Node_frame(ks,rs) -> ([0;List.length ks]@ks@rs)
            | Leaf_frame(kvs) -> (
                [1;List.length kvs]@(List.map fst kvs)@(List.map snd kvs))
          ) |> List.map Int32.of_int
          in
          let buf = Block.empty () in
          ints_to_bytes is buf;
          buf
      )

      let page_to_frame' : page -> pframe = (
        fun buf -> 
          let is = bytes_to_ints buf|>List.map Int32.to_int in
          match is with
          | 0::l::rest -> (
              let (ks,rs) = rest|>BatList.take (l+l+1)|>BatList.split_at l in
              Node_frame(ks,rs))
          | 1::l::rest -> (
              let (ks,vs) = rest|>BatList.take (2*l) |> BatList.split_at l in
              let kvs = List.combine ks vs in
              Leaf_frame(kvs)
            )
      )

      (* FIXME can remove these once code is trusted *)
      let frame_to_page = fun f -> 
        let p = frame_to_page' f in
        let f' = page_to_frame' p in
        let _ = assert (f' = f) in
        p

      let page_to_frame = fun p -> 
        let f = page_to_frame' p in
        let p' = frame_to_page' f in
        let _ = Bytes.([%test_eq: string] (to_string p) (to_string p')) in
        let _ = assert Bytes.(to_string p = to_string p') in
        f

    end (* FT *)

  end (* S *)

  include Btree.Make(S')

end
