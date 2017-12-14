theory Pre_insert
imports Find
begin



(* insert aux funs: split_leaf and split_node ----------------------- *)

(* FIXME these functions don't really belong here - they are a different kind
of splitting, based on size not search key *)

(* FIXME aren't these aux funs shared with its? *)

(* FIXME for insert_many we want to parameterize split_leaf so that it
results in a full left leaf *)

(* FIXME document *)

(* if a leaf is too big, we split it to get two leaves (lists of kv); we also return the separator
key k such that l < k \<le> r *)

(* FIXME split_at is inefficient *)
definition split_leaf :: "constants \<Rightarrow> ('k*'v)list \<Rightarrow> (('k*'v) list * 'k * ('k*'v) list)" where
"split_leaf c kvs = (
  let _ = check_true (% _. List.length kvs \<ge> c|>max_leaf_size+1) in
  (* FIXME what is the best choice? min is probably too small; could
  split in two, but what if order is not dense? we may never insert
  any more keys at this point *)
  (* FIXME following assumes leaf has size max_leaf_size+1, not anything more? *)
  let cut_point = (c|>max_leaf_size+1 - c|>min_leaf_size) in  
  let _ = check_true (% _ . cut_point \<le> List.length kvs) in
  let (l,r) = split_at cut_point kvs in 
  let _ = check_true (% _. List.length l \<ge> c|>min_leaf_size & List.length r \<ge> c|>min_leaf_size) in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible1 (STR ''key_value, split_leaf'')) in
  (l,k,r)
)"

(* let max and min be the relevant bounds; suppose node has max+1
keys; we could divide by 2 to get max+1/2; but here we try to get the
most in the left hand tree;

we need min in rhs; 1 for the middle, so we need max+1 -1 -min =
max-min in left (assumes that the node has max+1 size; obviously we
need to be more careful otherwise FIXME for bulk insert
*)

definition split_node :: 
  "constants \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'k * ('k list * 'a list)" 
where
"split_node c n = (
  let (ks,rs) = n in

  let cut_point = (c|>max_node_keys-c|>min_node_keys) in  
  (* FIXME see above; FIXME prefer to split equally even in insert_many case? *)

  let (ks1,k,ks2) = split_at_3 cut_point ks in
  let _ = check_true (% _. List.length ks2 \<ge> c|>min_node_keys) in
  let (rs1,rs2) = split_at (cut_point+1) rs in
  (* FIXME check that uses of split_leaf and split_node enforce wellformedness *)
  ((ks1,rs1),k,(ks2,rs2))
)"

end