
(* simple ------------------------------------------------------------ *)

(* this is a simplified interface *)

(* alternative that does one particular mapping from FT to bytes *)

open Btree
open Btree_util


(* NB page=bytes; sizeof block is in Sz *)
module type STORE = Btree.STORE with type page_ref=int and type page=bytes



(* sizes in int32, except b *)
(*
module type Sz_t = sig
  val b : int  (* size of block, in bytes *)
  val k : int
  val v : int
  val r : int
end
*)

(* input *)
module type S = Btree_api.Simple.S


module Make = functor (S:S) -> struct

  module S = S

  module KV=S.KV
  module ST=S.ST
  module C : CONSTANTS = struct
    open S
    let pp = S.pp
    let max_leaf_size = 
      ST.page_size - 4 - 4 (* for tag and length *)
                         / (pp.k_len+pp.v_len)
    let max_node_keys =
      ST.page_size - 4 - 4 - 4 (* tag, length x 2 *)
      - pp.v_len (* always one val more than # keys *)
        / (pp.k_len + pp.v_len)
    let min_leaf_size = 2
    let min_node_keys = 2
  end


  module FT = struct
    open KV
    open ST
    (* format: int node_or_leaf; int number of entries; entries *)


    type pframe =  
        Node_frame of (k_t list * page_ref list) |
        Leaf_frame of (k_t * v_t) list[@@deriving yojson]

    open Btree_util

    open S

    (* following assumes tags marshall to single int32 *)
    let node_tag = 0
    let leaf_tag = 1


    (* generic marshalling *)

    (* FIXME rewrite this *)

    let frame_to_page' : pframe -> page = Pickle.P.(
      fun p ->
        let is = Pickle.Examples.(
          match p with
          | Node_frame(ks,rs) -> (
              p_int node_tag |> bind (fun () -> 
                  p_list pp.p_k ks |> bind (fun () -> 
                      p_list p_int rs)))
          | Leaf_frame(kvs) -> (
              p_int leaf_tag |> bind (fun () -> 
                  let p = fun kv -> pp.p_k (fst kv) |> bind (fun () -> pp.p_v (snd kv)) in
                  p_list p kvs))
          )
        in
        let (_,s) = is "" in (* retrieve from monad *)
        let s = s ^ 
                (String.make (ST.page_size - String.length s) (Char.chr 0)) in
        s
    )

    let page_to_frame' : page -> pframe = Pickle.U.(
      fun buf -> 
        let x = Pickle.Examples.(
            u_int |> bind (fun tag -> 
                match tag with 
                | _ when tag = node_tag -> (
                    u_list pp.u_k |> bind (fun ks ->
                        u_list u_int |> bind (fun rs ->
                            ret (Node_frame(ks,rs)))))
                | _ when tag = leaf_tag -> (
                    let u = pp.u_k |> bind (fun k -> pp.u_v |> bind (fun v -> 
                        ret (k,v)))
                    in
                    u_list u |> bind (fun kvs -> 
                        ret (Leaf_frame(kvs)))))
          )
        in
        let (r,_) = x buf in
        r)

    (* FIXME can remove these once code is trusted *)
    let frame_to_page = fun f -> 
      let p = frame_to_page' f in
      let _ = Test.test (fun _ -> 
          let f' = page_to_frame' p in
          assert (f' = f)) 
      in
      p

    let page_to_frame = fun p -> 
      let f = page_to_frame' p in
      let _ = Test.test (fun _ -> 
          let p' = frame_to_page' f in
          assert Bytes.(to_string p = to_string p')) 
      in
      f

  end (* FT *)


  (* now we instantiate the btree functor *)

  module Main' = Main.Make(
    struct
      module C = C
      module KV = KV
      module ST = ST
      module FT = FT
    end)

end (* Make *)

