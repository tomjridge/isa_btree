(** Isabelle B-tree definitions, as an OCaml lib *)

(** {2 Public interfaces} *)

(** {2 Assertion checking etc} *)
include Isa_export_wrapper.Isa_export_assert_flag


(** {2 Constants} *)

type constants = Constants.constants =
  {
    min_leaf_size: int;
    max_leaf_size: int;
    min_node_keys: int;
    max_node_keys: int
  }

module Constants = Constants


(** {2 Disk-backed nodes} *)

include Isa_btree_intf.Dnode_type


(*
(** {2 Node/leaf conversions to/from lists} *)

include Isa_export_wrapper.Node_leaf_conversions_type

(*
include Isa_export_wrapper.Leaf_ops_type
include Isa_export_wrapper.Node_ops_type
*)
*)

(** {2 Pre-map ops} *)

include Isa_btree_intf.Pre_map_ops_type


(** {2 Insert many} *)

include Isa_export_wrapper.Insert_all_type

include Isa_export_wrapper.Insert_many_type

(** {2 Store ops} *)

include Isa_btree_intf.Store_ops_type


(** {2 Leaf stream ops} *)

include Isa_btree_intf.Leaf_stream_ops_type


(** {2 Main functionality: make_isa_btree} *)

(* include Isa_export_wrapper.Internal_export *)

(** {2 Internal interfaces} *)

module Isa_export = Isa_export
module Isa_export_wrapper = Isa_export_wrapper
