theory Tree_stack imports Tree begin
(* FIXME rename to stack? *)

(* treestack frame ------------------------------- *)

record 'a frame =
  f_ks1 :: "key list"
  f_ts1 :: "'a list"
  f_t :: 'a
  f_ks2 :: "key list"
  f_ts2 :: "'a list"
  
definition dest_frame :: "'a frame \<Rightarrow> (ks * 'a list) * 'a * (ks * 'a list)" where
"dest_frame f = (
  (f|>f_ks1,f|>f_ts1),
  f|>f_t,
  (f|>f_ks2, f|>f_ts2)
)"

type_synonym 'a stack = "'a frame list"  
type_synonym 'a stk = "'a stack" 

definition frame_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a frame \<Rightarrow> 'b frame" where
"frame_map g f = (
  \<lparr>
    f_ks1=(f|>f_ks1),
    f_ts1=(f|>f_ts1|>List.map g),
    f_t=(f|>f_t|>g),
    f_ks2=(f|>f_ks2),
    f_ts2=(f|>f_ts2|>List.map g)
  \<rparr>
)"


function stack_to_lu_of_child :: "'a stack \<Rightarrow> key option * key option" where
"stack_to_lu_of_child stk = (
  case stk of 
  [] \<Rightarrow> (None,None)
  | x#stk' \<Rightarrow> (
    let (l',u') = stack_to_lu_of_child stk' in
    let (ks1,ks2) = (x|>f_ks1,x|>f_ks2) in    
    let l = (if ks1 \<noteq> [] then Some(ks1|>List.last) else l') in
    let u = (if ks2 \<noteq> [] then Some(ks2|>List.hd) else u') in
    (l,u)
  )
)"
by(auto)

(* convert from tree to tstk ----------------------------------- *)

function tree_to_tstk :: "key \<Rightarrow> tree \<Rightarrow> tree stack" where
"tree_to_tstk k t = (
  case t of 
  Leaf _ \<Rightarrow> []
  | Node(ks,ts) \<Rightarrow> (
    let ((ks1,ts1),t',(ks2,ts2)) = split_ks_rs k (ks,ts) in
    let frm = \<lparr>f_ks1=ks1,f_ts1=ts1,f_t=t',f_ks2=ks2,f_ts2=ts2\<rparr> in
    (tree_to_tstk k t')@[frm]
  )
)"
by auto

(* convert to tree ------------------------------- *)


(* we may provide a new focus *)
function tstk_to_tree :: "tree \<Rightarrow> tree stack \<Rightarrow> tree" where
"tstk_to_tree fo ts = (
  case ts of 
  [] \<Rightarrow> fo
  | x#ts' \<Rightarrow> (
    let (ks1,ts1,_,ks2,ts2) = (x|>f_ks1,x|>f_ts1,(),x|>f_ks2,x|>f_ts2) in
    let fo' = Node(ks1@ks2,ts1@[fo]@ts2) in
    tstk_to_tree fo' ts' 
  )
)"
by auto


(* wellformed_tree_stack ---------------------------------------- *)


function wellformed_tree_stack :: "tree stack => bool" where
"wellformed_tree_stack tstk = assert_true tstk (
  case tstk of 
  Nil \<Rightarrow> True
  | c#xs \<Rightarrow> (
    let t = c|>f_t in
    wellformed_tree (Some Small_root_node_or_leaf) (tstk_to_tree t tstk))
)"
by auto


end
