theory Delete_tree_stack
imports Tree Insert_tree_stack
begin
(*I need new datatypes in tree stack*)



(*BEGIN -this should go in the Utils theory*)
(*remove nth from list*)
fun remove_at :: "nat => 'a list => 'a list" where
"remove_at i [] = []" |
"remove_at 0 (x#xs) = xs" |
"remove_at (Suc i) (x#xs) = x#(remove_at i xs)"

definition remove_key_child :: "nat => Tree => Tree" where
"remove_key_child i t == (
case t of 
Leaf ls => Leaf (remove_at i ls)
| Node (ks,rs) => (*when I remove from a Node, there has been a merge, so I know I MUST delete a key and a child*)
  (*also, I know that the index is always i.e. j+1*)
  Node((remove_at (i-1) ks),(remove_at i rs))
)
"
(*END - this should go in the Utils theory*)

(*BEGIN - this should go in a del_tree_stack theory*)

(*begin delete types*)
datatype was_stolen_right = Was_stolen_right "bool"

datatype up_or_delete =
DUp "Tree"
| DUp_after_stealing "(Tree * Tree * key * was_stolen_right)" (*stealing_node,stolen_node,rotating_key,was_stolen_right*)
| DDelete "(Tree * nat)"

type_synonym del_focus_t = "up_or_delete"

datatype del_tree_stack = Del_tree_stack "del_focus_t * context_t"

definition dest_del_ts :: "del_tree_stack => (del_focus_t * context_t)" where
"dest_del_ts dts== (
case dts of Del_tree_stack ts => ts)
"
(*end delete types*)
definition is_too_slim :: "Tree => bool" where
"is_too_slim t = (
case t of
Leaf xs =>
 let leaf_size = length xs in
 (1 < leaf_size) & (leaf_size < min_leaf_size)
| Node (ks,_) =>
 let node_keys = length ks in
 (1 < node_keys) & (node_keys < min_node_keys)
)
"

definition is_fat :: "Tree => bool" where
"is_fat t = (
case t of
Leaf xs =>
 let leaf_size = length xs in
 (1 < leaf_size) & (min_leaf_size < leaf_size)
| Node (ks,_) =>
 let node_keys = length ks in
 (1 < node_keys) & (min_node_keys < node_keys)
)"


(*steal_right assumes that Trees are not empty and balanced *)
definition steal_right :: "Tree => Tree => (node_lbl_t * Tree list) => nat => del_focus_t" where
"steal_right r_sibling sibling parent sibling_index_in_parent = (
let (ks,rs) = parent in
(*add first key and value/child of the right sibling to the end of sibling (after deletion)*)
let (rotating_key,sibling') = 
(case (sibling,r_sibling) of
(Node (s_ks,s_rs), Node ((fst_k#_),(fst_r#_))) =>
(fst_k,Node((s_ks@[ks!sibling_index_in_parent]),(s_rs@[fst_r])))
| _ => undefined)
in
(*remove first key and child of the right sibling*)
let r_sibling' = remove_key_child 0 r_sibling in
DUp_after_stealing (sibling',r_sibling',rotating_key,(Was_stolen_right True))
)"

(*steal_left assumes that Trees are not empty and balanced *)
definition steal_left :: "Tree => Tree => (node_lbl_t * Tree list) => nat => del_focus_t" where
"steal_left l_sibling sibling parent sibling_index_in_parent = (
let (ks,rs) = parent in
let last_index_l_sibling = 
(case l_sibling of
Leaf l => length l
| Node (l,_) => length l)
in
(*add last key and value/child of the left sibling to the beginning of sibling*)
let (rotating_key,sibling') = 
(case (sibling,l_sibling) of
(Node (s_ks,s_rs), Node (ls_ks,ls_rs)) =>
let key = ls_ks!last_index_l_sibling in
let sibling_keys = ((ks!(sibling_index_in_parent-1))#s_ks) in
let sibling_children = (rs!last_index_l_sibling)#s_rs in
(key,Node(sibling_keys,sibling_children))
| _ => undefined)
in
(*remove last key and child of the right sibling*)
let l_sibling' = remove_key_child last_index_l_sibling l_sibling in
DUp_after_stealing(sibling',l_sibling',rotating_key,(Was_stolen_right False))
)"

(*merge_right assumes that Trees are not empty and balanced *)
definition merge_right :: "Tree => Tree => (node_lbl_t * Tree list) => nat => del_focus_t" where
"merge_right r_sibling sibling parent sibling_index_in_parent = (
let (ks, rs) = parent in
(*merge nodes*)
let sibling' =
(case (sibling, r_sibling) of
(*NB: the leaf case will be treated in the step across*)
(Node (sks, srs), Node (rsks, rsrs)) =>
(*when I merge nodes, I need to import a key separating the last and first child of the nodes*)
Node ((sks@((ks!sibling_index_in_parent)#rsks)), (srs@rsrs))
| _ => undefined)
in
DDelete(sibling',(sibling_index_in_parent+1))
)"

(*merge_left assumes that Trees are not empty and balanced *)
definition merge_left :: "Tree => Tree => (node_lbl_t * Tree list) => nat => del_focus_t" where
"merge_left l_sibling sibling parent sibling_index_in_parent = (
let (ks, rs) = parent in
(*merge nodes*)
let sibling' =
(case (sibling, l_sibling) of
(Node (sks, srs), Node (lsks, lsrs)) =>
(*when I merge nodes, I need to import a key separating the last and first child of the nodes*)
Node ((lsks@((ks!(sibling_index_in_parent-1))#sks)), (lsrs@srs))
| _ => undefined)
in
DDelete(sibling',sibling_index_in_parent)
)"

(*begin step del tree stack*)
definition update_del_focus_at_position :: "(node_t * nat) => (node_t * nat) => del_focus_t => del_focus_t" where
"update_del_focus_at_position ni ni' f == (
let (n,i) = ni in
let (ks,rs) = n in (*focus parent*)
case f of
DUp t => 
(let rs2 = list_update rs i t in
DUp(Node(ks,rs2)))
| DUp_after_stealing(stealing_sibling,stolen_sibling,rotating_key,(Was_stolen_right wsr)) => (
let stolen_index = (if wsr then (i+1) else (i-1)) in
let rotating_index = (if wsr then i else (i-1)) in
(*update parent with siblings *)
let rs1 = list_update rs stolen_index stealing_sibling in
let rs2 = list_update rs1 stolen_index stolen_sibling in
(*replace parent key*)
let ks1 = list_update ks rotating_index rotating_key in
DUp(Node(ks1,rs2)))
| DDelete (t,d_index) =>
let (n',i') = ni' in
let (pks,prs) = n' in (*focus grandparent*)
(* I add the merged child to the focus parent*)
let rs1 = (list_update rs i t) in 
(* I delete the half merged to the child and the relating key from the focus parent *)
let t' = (remove_key_child d_index (Node(ks,rs1))) in
(*now the focus parent may need restructuring *)
(case is_too_slim t' of
False => (*no restructuring*)
(DUp t')
| True => (
(*in this case I can both steal or merge.
  
  * I will steal if the right sibling is not slim or the left sibling is not slim;

  * otherwise, I will merge with the right sibling, if it exists, or with the left sibling.
*)
(*NB: these restructuring happen only on internal nodes, leaves will be treated in the step across definitions!!*)
let m_right_sibling = (if (i' = (length pks)) then None else Some(prs!(i'+1))) in
let m_left_sibling  = (if (i' = 0) then None else Some(prs!(i'-1))) in
(case ((is_Some m_right_sibling) & (is_fat (dest_Some m_right_sibling))) of
True => ( (*STEAL RIGHT*)
let right_sibling = dest_Some m_right_sibling in
steal_right right_sibling t' (pks,prs) i)
| False => 
(case ((is_Some m_left_sibling) & (is_fat (dest_Some m_left_sibling))) of
True => ( (*STEAL LEFT*) 
let left_sibling = dest_Some m_left_sibling in
steal_left left_sibling t' (pks,prs) i)
| False =>
(case (is_Some m_right_sibling) of
True => ( (*MERGE RIGHT*)
let right_sibling = dest_Some m_right_sibling in
merge_right right_sibling t' (pks,prs) i')
| False => ( (*MERGE LEFT*)
let left_sibling = dest_Some m_left_sibling in
merge_left left_sibling t' (pks,prs) i))
))))
)
"


definition step_del_tree_stack :: "del_tree_stack => del_tree_stack option" where
"step_del_tree_stack ts == (
let (f,stk) = dest_del_ts ts in
case stk of 
Nil => None
| ((lb,(n,i),rb)#Nil) => (*ROOT may be not well formed (i.e. redundant child)*)
(case f of
DUp _ => None
| DDelete(t,i) =>
(case t of
Leaf l =>
(* we assume that the step across does the following:
```
 let f1 = DUp (remove_key_child i t) in
 Some(Del_tree_stack(f1,Nil))
```
so we just return:
*)
None
| Node (ks,rs) => (*this means we merged a node before, and we need to update i-1*)
let f1 =
(if (length ks = 1) 
then (DUp(Node(ks,rs)))
else
let (pks,prs) = n in
let prs' = list_update prs (i-1) (Node(ks,rs)) in
let t' = Node(pks,prs') in
(DUp(remove_key_child i t')))
in
Some(Del_tree_stack(f1,Nil))
))
| ((lb,(n,i),rb)#((lb',(n',i'),rb')#xs)) => (
let f2 = update_del_focus_at_position (n,i) (n',i') f in
Some(Del_tree_stack(f2,((lb',(n',i'),rb')#xs))
))
)
"
(*end step del tree stack*)
(*END*)

(*BEGIN delete wf statements*)
definition wellformed_del_focus :: "del_focus_t => bool => bool" where
"wellformed_del_focus f stack_empty == (
case f of
DUp t => wellformed_tree (Rmbs stack_empty) t
(*here on the Rmbs are false because step_del_tree_stack set the focus always to a DUp when the stack is empty*)
| DUp_after_stealing(stealing_sibling,stolen_sibling,key,(Was_stolen_right wsr)) => (
wellformed_tree (Rmbs False) stealing_sibling
& wellformed_tree (Rmbs False) stolen_sibling
& 
(if wsr 
then 
 (check_keys None (keys stealing_sibling) (Some key)
 & check_keys (Some key) (keys stolen_sibling) None)
else
 (check_keys None (keys stolen_sibling) (Some key)
 & check_keys (Some key) (keys stealing_sibling) None))
)
| DDelete (t,i) => (
wellformed_tree (Rmbs False) t
& (case t of Leaf l => i < length l | Node (_,rs) => i < length rs))
)"

definition wellformed_del_ts1 :: "del_tree_stack => bool" where
"wellformed_del_ts1 dts == (
let (f,stk) = dest_del_ts dts in
(case stk of
Nil => True
| ((lb,((l,cs),i),rb)#r_stk) =>
let (kl,kr) = get_lower_upper_keys_for_node_t (lb,((l,cs),i),rb) in
(case f of
DUp t => (
(* size not checked; we assume focus is wf *)
let b1 = True in
(* ksrs fine *)
let b2 = True in
let b3 = (height (cs!i) = height t) in
let b4 = (check_keys kl (keys t) kr)
in
(* keys ordered *)
let b5 = True in
let wf = b1&b2&b3&b4&b5 in
wf)
| DUp_after_stealing (stealing_sibling,stolen_sibling,key,(Was_stolen_right wsr)) => (
(* size not checked; we assume focus is wf *)
let b1 = True in
(* ksrs fine *)
let b2 = True in
let b3 =
(height (cs!i) = height stealing_sibling)
& (height (cs!i) = height stolen_sibling)
in
let b4 =
(check_keys kl (keys stealing_sibling) kr)
&
(check_keys kl (keys stolen_sibling) kr)
in
(* keys ordered *)
let b5 = True in
let wf = b1&b2&b3&b4&b5 in
wf)
| DDelete(t,d_i) => (
(* size not checked; we assume focus is wf *)
let b1 = True in
(* ksrs fine *)
let b2 = True in
let b3 = (height (cs!i) = height t) in
let b4 = (check_keys kl (keys t) kr)
in
(* keys ordered *)
let b5 = True in
let wf = b1&b2&b3&b4&b5 in
wf))
)
)"

definition wellformed_del_ts :: "del_tree_stack => bool" where
"wellformed_del_ts ts == (
let (f,stk) = dest_del_ts ts in
wellformed_del_focus f (stk=[])
& wellformed_context stk
(* maybe later..
& wellformed_del_ts_1 ts*))"
(*END delete wf statements*)
end