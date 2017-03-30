theory Frame
imports Key_value
begin

(* blocks on disk correspond to frames, which are like tree nodes, but with pointers rather than
children *)

type_synonym store_ptr = nat
type_synonym r = store_ptr
type_synonym rs = "r list"

datatype ('k,'v) t = Node_frame "'k list * r list" | Leaf_frame "('k*'v) list"
type_synonym pfr = "(key,value_t) t"

definition dest_Node_frame :: "('k,'v) t \<Rightarrow> ('k list * r list)" where
"dest_Node_frame f = (case f of Node_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Node_frame''))"

definition dest_Leaf_frame :: "('k,'v) t \<Rightarrow> ('k*'v) list" where
"dest_Leaf_frame f = (case f of Leaf_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Leaf_frame''))"


(* insert aux funs --------------------------------------------------------------- *)

(* FIXME aren't this aux funs shared with its? *)
definition split_leaf :: "nat \<Rightarrow> nat \<Rightarrow> ('k*'v)list \<Rightarrow> (('k*'v)list * 'k * ('k*'v) list)" where
"split_leaf min_leaf_size max_leaf_size kvs = (
  (* FIXME what is the best choice? min is probably too small; could split in two, but what if order is not dense? we may never insert any more keys at this point *)
  (* FIXME following assumes leaf has size max_leaf_size+1, not anything more? *)
  let cut_point = (max_leaf_size+1 - min_leaf_size) in  
  let (l,r) = split_at cut_point kvs in 
  let _ = assert_true' (List.length l \<ge> min_leaf_size & List.length r \<ge> min_leaf_size) in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible1 (STR ''key_value, split_leaf'')) in
  (l,k,r)
)"

(* let max and min be the relevant bounds; suppose node has max+1 keys; we could divide by 2 to get
max+1/2; but here we try to get the most in the left hand tree; 

we need min in rhs; 1 for the middle, so we need max+1 -1 -min = max-min in left (assumes that the node has
max+1 size; obviously we need to be more careful otherwise FIXME for bulk insert

*)

definition split_node :: 
  "nat \<Rightarrow> nat \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'k * ('k list * 'a list)" where
"split_node min_node_keys max_node_keys n = (
  let (ks,rs) = n in
  let cut_point = (max_node_keys-min_node_keys) in  (* FIXME see above *)
  let (ks1,k,ks2) = split_at_3 cut_point ks in
  let _ = assert_true' (List.length ks2 \<ge> min_node_keys) in
  let (rs1,rs2) = split_at (cut_point+1) rs in
  ((ks1,rs1),k,(ks2,rs2))
)"

end