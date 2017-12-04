theory Find 
imports "$SRC/b_store_monad/Monad"
begin

type_synonym ('k,'r) rstk = "('k,'r) ts_frame list"

type_synonym 'a s = "'a list"


(* find ------------------------------------------------------------- *)

datatype ('k,'v,'r) find_state = 
  F_down "'r * 'k * 'r * ('k,'r) rstk"  (* root, search key, current pointer, stack *) 
  | F_finished "'r * 'k * 'r * ('k*'v)s * ('k,'r)rstk"

type_synonym ('k,'r) f_down = "'r * 'k * 'r * ('k,'r)rstk"
type_synonym ('k,'v,'r) f_finished = "'r * 'k * 'r * ('k*'v)s * ('k,'r)rstk"
type_synonym ('k,'v,'r) fs = "('k,'v,'r) find_state"
type_synonym ('k,'r) fo = "'k*'r"  (* focus *)

  
  
definition dest_f_finished :: "('k,'v,'r)fs \<Rightarrow> ('k,'v,'r)f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk)  
)"



definition mk_find_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)fs" where
"mk_find_state k r = F_down(r,k,r,[])"



definition find_step :: "('k,'v,'r,'t)ps1 \<Rightarrow> ('k,'v,'r)fs \<Rightarrow> (('k,'v,'r)fs,'t) MM" where
"find_step ps1 fs = (
  let store_ops = ps1 |> ps1_store_ops in
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(r0,k,r,stk) \<Rightarrow> (
    (store_ops|>store_read) r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let (stk',r') = add_new_stack_frame (ps1|>cmp_k) k (ks,rs) stk in
        F_down(r0,k,r',stk')
      )
      | Leaf_frame kvs \<Rightarrow> (F_finished(r0,k,r,kvs,stk)))) )"



(* wellformedness --------------------------------------------------- *)

(* like to have this in a "programmatic" style; so convert a store
into a map from r * nat to tree option, then check the r with a t ,
given t height *)



definition wf_store_tree :: "('k,'v,'r,'t)r2t \<Rightarrow> 't \<Rightarrow> 'r \<Rightarrow> ('k,'v)tree \<Rightarrow> bool" where
"wf_store_tree r2t s r t = assert_true (
  case r2t s r of
  None \<Rightarrow> False
  | Some t' \<Rightarrow> (tree_equal t t'))"



(* t0 is the tree we expect *)
definition wellformed_find_state :: "'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> ('k,'v,'r)fs \<Rightarrow> bool" where
"wellformed_find_state k_ord r2t t0 s fs = assert_true (
  let n = height t0 in
  (* need to check the stack and the focus *)
  let check_focus = % r t. wf_store_tree r2t s r t in
  let check_stack = % rstk tstk. stack_equal (tstk |> stack_map Some) (rstk |> stack_map (r2t s)) in 
  case fs of 
  F_finished (r0,k,r,kvs,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k_ord k t0 (List.length stk) in
    assert_true (check_focus r t_fo) &
    assert_true (check_stack stk t_stk))
  | F_down (r0,k,r,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k_ord k t0 (List.length stk) in
    assert_true (check_focus r t_fo) &
    assert_true (check_stack stk t_stk) ))"



(* testing ---------------------------------------------------------- *)

(* really wf_trans is trivial, but for testing we check some obvious properties *)

(* FIXME probably not worth doing *)
definition wf_trans :: "'t * ('k,'v,'r)fs \<Rightarrow> 't * ('k,'v,'r)fs \<Rightarrow> bool" where
"wf_trans s1 s2 = assert_true (
  let (s1,fs1) = s1 in
  let (s2,fs2) = s2 in
  (* FIXME dont want to force equality check of the store (s2=s1) & *)
  (case (fs1,fs2) of
  (F_down(r0,k,r,stk),F_down(r0',k',r',stk')) \<Rightarrow> (List.length stk' = 1+List.length stk)
  | (F_down(_),F_finished(_)) \<Rightarrow> True
  | _ \<Rightarrow> False) )"

end










(* old =========================================================


(* find_trans *)

(*
definition find_trans :: "(store * fs) trans_t" where
"find_trans = { ((s,fs),(s',fs')). ( s|>(find_step fs|>dest_M) = (s',Ok fs')) }"
*)

(* lemmas *)

(* wf_fts is invariant *)
(*
definition invariant_lem :: "bool" where
"invariant_lem = (
  ! P s t0. 
  ((% s_fs. let (_,fs) =  s_fs in wellformed_find_state s t0 fs) = P) \<longrightarrow> invariant find_trans P)"
*)

*)