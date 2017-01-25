(* simple in-mem implementation, mainly for testing ----------------------------- *)

(* NB pages are not simple byte arrays; they are frames; this avoids
   need to fiddle with frame<->page mappings 


   We are parametric over KV and C

*)


let failwith x = failwith ("in_mem: "^x)

(* we concentrate on relatively small parameters *)


(* setup ---------------------------------------- *)

open Btree


module type S = sig

  module KV : Btree.KEY_VALUE_TYPES
  module C : Btree.CONSTANTS  

end


module Map_int = Btree_util.Map_int


module Make = functor (S:S) -> struct

  module Private = struct

    module S = S

    open S


    module PR = struct 
      type page_ref = int[@@deriving yojson]
    end


    module FT = struct

      open KV
      open PR

      type pframe =  
          Node_frame of (key list * page_ref list) |
          Leaf_frame of (key * value_t) list[@@deriving yojson]

      type page = pframe[@@deriving yojson]

      let frame_to_page : pframe -> page = fun x -> x
      let page_to_frame : page -> pframe = fun x -> x

    end


    module ST' = struct

      open FT
      open PR

      type page = FT.page

      type store = {free:int; m:page Map_int.t}

      (* for yojson *)
      type store' = {free':int; m':(int * page) list}[@@deriving yojson]

      let store_to_' s = {free'=s.free; m'=s.m|>Map_int.bindings}

      type store_error = unit

      let dest_Store : store -> page_ref -> page = (fun s r -> Map_int.find r s.m)

      let page_ref_to_page r s = (s,Our.Util.Ok(Map_int.find r s.m))

      let alloc p s = (
        let f = s.free in
        ({free=(f+1);m=Map_int.add f p s.m}),Our.Util.Ok(f))

      let free :
        page_ref list -> store -> store * (unit, store_error) Our.Util.rresult = (
        fun ps s -> (s,Our.Util.Ok(())))

    end (* ST' *)


    module ST (* : STORE *) = struct
      include PR
      include ST'
    end


    module S' (* : Btree.S *) = struct

      module C = C

      module KV = KV

      module ST = ST

      module FT = FT

    end


    module Btree' = Btree.Make(S')
    
  end (* Private *)


  include Private.Btree'


end  (* Make *)


(* example int int btree ---------------------------------------- *)

module Example = struct 

  module C : CONSTANTS = struct
    let max_leaf_size = 5
    let max_node_keys = 5
    let min_leaf_size = 2
    let min_node_keys = 2
  end


  module KV (* : KEY_VALUE_TYPES *) = struct 
    type key = int[@@deriving yojson]
    type value_t = int[@@deriving yojson]
    let key_ord k1 k2 = Pervasives.compare k1 k2
    let equal_value = (=)
  end


  include Make(struct module C=C module KV=KV end)


  let empty = Map_int.empty


end
