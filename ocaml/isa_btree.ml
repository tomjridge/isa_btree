(** Isabelle B-tree definitions, as an OCaml lib *)

(** {2 Public interfaces} *)

type constants = Constants.constants =
  {
    min_leaf_size: int;
    max_leaf_size: int;
    min_node_keys: int;
    max_node_keys: int
  }

module Constants = Constants

include Isa_export_wrapper.Node_leaf_conversions_type
include Isa_export_wrapper.Internal_export

(** {2 Internal interfaces} *)

module Isa_export = Isa_export
module Isa_export_wrapper = Isa_export_wrapper
