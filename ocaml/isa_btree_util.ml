(** Given a value [k_cmp], construct the corresponding map_ops, with
   keys: k, k option *)

open Tjr_map.With_base_as_record

open Isa_btree_intf
(* open Isa_btree_intf.Leaf_node_frame_map_ops_type *)

module Internal_make_map_ops(S:sig type k val k_cmp: k->k->int end) = struct
  open S
  module K_comp = Base.Comparator.Make(struct
      type t = k
      let compare = k_cmp
      let sexp_of_t f = failwith __LOC__
    end)

  type k_comparator = K_comp.comparator_witness

  (* Base.Map.comparator is different from Comparator.comparator *)
  let k_comparator : (k,k_comparator)Base.Map.comparator = 
    (module struct type t = k include K_comp end)      
    

  let k_map () :(k,'v,_) Leaf_node_frame_map_ops_type.map_ops = 
    make_map_ops k_comparator 

  module Kopt_comp = Base.Comparator.Make(struct
      type t = k option

      (* None is less than any other lower bound; this corresponds to the
         "lowest" interval below k0 *)
      let rec kopt_compare k1 k2 =
        match k1,k2 with 
        | None,None -> 0
        | None,_ -> -1
        | _,None -> 1
        | Some k1, Some k2 -> k_cmp k1 k2

      let compare = kopt_compare
      let sexp_of_t f = failwith __LOC__
    end)

  type kopt_comparator = Kopt_comp.comparator_witness

  let kopt_comparator : (k option,kopt_comparator)Base.Map.comparator = 
    (module struct type t = k option include Kopt_comp end)

  let kopt_map () : (k option,'r,_)Leaf_node_frame_map_ops_type.map_ops = 
    make_map_ops kopt_comparator 

end

(** For testing *)
module Int_map_ops = Internal_make_map_ops(
  struct type k = int let k_cmp=Pervasives.compare end)

(** Utility function to convert a comparator to a record of map operations. *)
module Comparator_to_map_ops = struct
  let comparator_to_map_ops (cmp:('k,'cmp)Base.Map.comparator) =
    Tjr_map.With_base_as_record.make_map_ops cmp
end
include Comparator_to_map_ops
