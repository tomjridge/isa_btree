theory Params
imports Pre_params
begin

(* a store is a map from page_ref to frame *)
typedecl page_ref
type_synonym r = page_ref
type_synonym rs = "r list"


(* fix a particular k v *)
datatype k = K nat
datatype v = K nat


type_synonym ks = "k list"
type_synonym kv = "k*v"
type_synonym kvs = "kv list" 
type_synonym vs = "v list"


(* fix order *)

definition compare_k :: "k key_order" where
"compare_k = \<lparr> lt=(% k1 k2. failwith (STR ''FIXME'')) \<rparr>"

type_synonym kv_tree = "(k,v) tree"

(* fix constants *)
definition constants :: constants where
"constants = \<lparr>
min_leaf_size=0,
max_leaf_size=0,
min_node_keys=0,
max_node_keys=0
\<rparr>"



(* store frame *)
type_synonym frame = "(k,v,r) Frame.t"

(* to force Frame early *)
(* definition dest_Node_frame :: "frame \<Rightarrow> ks * rs" where "dest_Node_frame = Frame.dest_Node_frame" *)

(* store type ----------------------- *)

typedecl store

(* for testing *)

type_synonym r2f = "r \<Rightarrow> frame option"

(* debugging/proof *)
definition "mk_r2f" :: "store \<Rightarrow> r2f" where
"mk_r2f s = failwith (STR ''FIXME'')"

(* monad *)
datatype 'a MM = MM "(store \<Rightarrow> store * 'a res)" 

(* store api -------------------------------------------------- *)

definition "store_read" :: "r \<Rightarrow> frame MM" where
"store_read r = failwith (STR ''FIXME'')"

definition "store_alloc" :: "frame \<Rightarrow> r MM" where
"store_alloc frm = failwith (STR ''FIXME'')"

definition "store_free" :: "r list \<Rightarrow> unit MM" where
"store_free rs = failwith (STR ''FIXME'')" 



type_synonym rstk = "(k,r) ts_frame list"
  

type_synonym tstk = "(k,kv_tree) tree_stack" (* FIXME replace with tree_stack *)
end