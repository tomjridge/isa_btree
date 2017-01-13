(* a map from int to int; Store.page=bytes --------------------------------- *)

(* FIXME error handlign *)

open Sexplib.Std  (* for ppx_assert *)

let failwith x = failwith ("int_int_store: "^x)

open Block_device

open Btree_util

(* assumptions ---------------------------------------- *)

let block_size = Block.size

let int_size = 4  (* bytes *)


(* KV, C, STORE, FT --------------------------------------- *)

module KV = struct
  type key = int[@@deriving yojson]
  type value_t = int[@@deriving yojson]
  let key_ord (x:int) y = Pervasives.compare x y
  let equal_value x y = (x=y)
end


module C = struct

  (* if n keys, we need 2+n+(n+1) ints to store; n = block_size/4 -2 - 1 / 2 *)
  let max_node_keys = (block_size / int_size - 2 - 1)/2
  let max_leaf_size = (block_size / int_size - 2)/2
  let min_node_keys = 2
  let min_leaf_size = 2
end


(* NB page=bytes *)
module type STORE = Btree.STORE with type page_ref=int and type page=bytes


module Make = functor (ST:STORE) -> struct

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


(* frame mapping for int int kv ---------------------------------------- *)

(* ties together C, KV, store and frame maps *)

(* from here, we specialize to the following filestore *)
module ST = Recycling_filestore

module Int_int_filestore (* : Btree.S *) = struct

  include Make(ST)

  let existing_file_to_new_store = (
    let open S in
    let open ST in
    let open FT in
    let f : string -> store * page_ref = (
      fun s ->
        let fd = Blk_fd.open_file s in
        (* now need to write the initial frame *)
        let frm = Leaf_frame [] in
        let p = frm|>frame_to_page in
        let r = 0 in
        let () = Blk_fd.write fd r p in

        Recycling_filestore.(
          {fs = Filestore.{fd=fd;free_ref=r+1} ;
           cache=Cache.empty;
           freed_not_synced=Set_int.empty;
          },r)

      (*        
        Filestore.({ fd=fd; free_ref = r+1},r)
*)
    )
    in
    f)

end



(* a high-level cache over Insert_many -------------------------------------- *)

(* we cache at the map level *)

module Int_int_cached (* : Btree.S *) = struct

  open Int_int_filestore

  type kvs = (KV.key * KV.value_t) list

  type pending_inserts = int Map_int.t  (* the high-level cache *)

  type t = ST.page_ref * ST.store * pending_inserts

  module Insert = struct

    (* just add to cache *)
    let insert : KV.key -> KV.value_t -> t -> t = (
      fun k v t -> 
        let (r,s,ps) = t in
        let ps' = Map_int.add k v ps in
        (r,s,ps'))

  end

  let sync : t -> t = (
    fun t -> 
      let (r,s,kvs) = t in
      (* insert all that are in the cache, using insert_many.cache *)
      let kvs = Map_int.bindings kvs in
      match kvs with 
      | [] -> (
          let () = ST.sync s in
          (r,s,Map_int.empty))
      | _ -> (  
          let f (s,r,kvs) = (
            match kvs with
              [] -> None
            | (k,v)::kvs -> (
                let (s,(r,kvs)) = Insert_many.insert k v kvs r s in
                Some(s,r,kvs)))
          in
          let (s,r,kvs) = Btree.iter_step f (s,r,kvs) in
          let () = ST.sync s in
          (r,s,Map_int.empty)
        )
  )



end

