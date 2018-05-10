theory Find_state
imports Pre_monad
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"


(* we put all the types that we want "outside" the monad, but which really belong with Find, 
Insert, etc., here *)

(* we use a small-step style; we reify the state of the algorithm at every
step as the following state type *)

(* find ----------------------------------------------------------------------- *)

datatype ('k,'v,'r) find_state = 
  F_down "'r * 'k * 'r * ('k,'r) rstk"  (* root, search key, current pointer, stack *) 
  | F_finished "'r * 'k * 'r * ('k*'v)s * ('k,'r)rstk"



type_synonym ('k,'r) f_down = "'r * 'k * 'r * ('k,'r)rstk"
type_synonym ('k,'v,'r) f_finished = "'r * 'k * 'r * ('k*'v)s * ('k,'r)rstk"
type_synonym ('k,'v,'r) fs = "('k,'v,'r) find_state"

(* type_synonym ('k,'r) fo_unused = "'k*'r"  (* focus *) *)

  
  
definition dest_f_finished :: "('k,'v,'r)fs \<Rightarrow> ('k,'v,'r)f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk) )"



definition mk_find_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)fs" where
"mk_find_state k r = F_down(r,k,r,[])"


(* wellformedness --------------------------------------------------- *)

(* like to have this in a "programmatic" style; so convert a store
into a map from r * nat to tree option, then check the r with a t ,
given t height *)

(* given a store s, a block ref r, and a tree t, return true if the store 
from r represents the tree t *)

definition wf_store_tree :: "('k,'v,'r,'t)r2t \<Rightarrow> 't \<Rightarrow> 'r \<Rightarrow> ('k,'v)tree \<Rightarrow> bool" where
"wf_store_tree r2t s r t = assert_true (
  case r2t s r of
  None \<Rightarrow> False
  | Some t' \<Rightarrow> (tree_equal t t'))"



(* given an expected tree t0, a store s, and a find state fs,
check that the find state is wellformed and consistent with the
store *)
definition wellformed_find_state :: 
  "'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> ('k,'v,'r)fs \<Rightarrow> bool" 
where
"wellformed_find_state k_ord r2t t0 s fs = assert_true (
  let n = height t0 in
  (* need to check the stack and the focus *)
  let check_focus = % r t. wf_store_tree r2t s r t in
  let check_stack = 
    % rstk tstk. rstack_equal (tstk |> rstack_map Some) (rstk |> rstack_map (r2t s)) in 
  case fs of 
  F_finished (r0,k,r,kvs,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    assert_true (check_focus r t_fo) &
    assert_true (check_stack stk t_stk))
  | F_down (r0,k,r,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    assert_true (check_focus r t_fo) &
    assert_true (check_stack stk t_stk) ))"



(* testing ---------------------------------------------------------- *)

(* really wf_trans is trivial, but for testing we check some obvious properties *)

(* FIXME probably not worth doing *)
definition wf_trans :: "'t * ('k,'v,'r)fs \<Rightarrow> 't * ('k,'v,'r)fs \<Rightarrow> bool" where
"wf_trans s1 s2 = assert_true (
  let (s1,fs1) = s1 in
  let (s2,fs2) = s2 in
  (* FIXME don't want to force equality check of the store (s2=s1) & *)
  case (fs1,fs2) of
  (F_down(r0,k,r,stk),F_down(r0',k',r',stk')) \<Rightarrow> (List.length stk' = 1+List.length stk)
  | (F_down _,F_finished _) \<Rightarrow> True
  | _ \<Rightarrow> False)"

end