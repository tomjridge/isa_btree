theory Export_code
imports Find_tree_stack Insert_tree_stack "~~/src/HOL/Library/Code_Target_Numeral"
begin


code_printing
  code_module "Hack" => (OCaml)
"module X = struct

type key = string
type valuet = int

let min_leaf_size=2
let max_leaf_size=4
let min_node_keys=2
let max_node_keys=4

let keyord k1 k2 = Pervasives.compare k1 k2  

end"


export_code "Code_Numeral.nat_of_integer" "Code_Numeral.int_of_integer" mk_fts step_fts dest_fts mk_its step_its dest_its in OCaml file "ocaml/btree_generated.ml"

end