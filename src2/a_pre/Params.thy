theory Params
imports Key_value Frame
begin

(* a store is a map from page_ref to frame *)
typedecl page_ref
type_synonym r = page_ref
type_synonym rs = "r list"


(* fix a particular k v *)
datatype k = K nat
datatype v = V nat

type_synonym ks = "k list"
type_synonym kv = "k*v"
type_synonym kvs = "kv list" 
type_synonym vs = "v list"


(* fix order *)
definition ord0 :: "k key_order" where
"ord0 k1 k2 = failwith (STR ''FIXME'')"

definition keq :: "k \<Rightarrow> k \<Rightarrow> bool" where
"keq k1 k2 = failwith (STR ''FIXME'')"

(* fix constants *)
definition cs0 :: constants where
"cs0 = \<lparr>
min_leaf_size=0,
max_leaf_size=0,
min_node_keys=0,
max_node_keys=0
\<rparr>"

(* store frame *)
type_synonym frame = "(k,v,r) Frame.t"

(* store type ----------------------- *)

typedecl store


end