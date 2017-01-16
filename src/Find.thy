theory Find 
imports Monad2 (* FIXME for sktoi; move to kv *)
begin

(* empty ----------------------------------------------------------------------- *)

(* we put this here because this is the "start" of the interface defns for the btree *)

definition empty_btree :: "unit \<Rightarrow> r MM" where
"empty_btree _ = (
  (* empty leaf *)
  let lf = Leaf_frame([]) in
  lf |> frame_to_page |> alloc 
)"



(* find ------------------------------------------------------------------------- *)

type_synonym stk = "r stk"

datatype find_state = 
  F_down "r*k*r*stk"  (* root, search key, lower and upper bound for r *) 
  | F_finished "r*k*r*kvs*stk"

type_synonym d = "r*k*r*stk"
  
type_synonym fo = "k*r"  (* focus *)
  
type_synonym f_finished = "r*k*r*kvs*stk"

type_synonym fs = find_state
  
definition dest_f_finished :: "find_state \<Rightarrow> f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk)  
)"

definition mk_find_state :: "key \<Rightarrow> r \<Rightarrow> find_state" where
"mk_find_state k r = F_down(r,k,r,[])"

(* FIXME maybe want to store ks,rs as a list of (k,r), with the invariant that the last k is +inf *)

definition find_step :: "fs \<Rightarrow> fs MM" where
"find_step fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(r0,k,r,stk) \<Rightarrow> (
    page_ref_to_frame r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let (stk',r') = add_new_stk_frame k (ks,rs) stk in
        F_down(r0,k,r',stk')
      )
      | Leaf_frame kvs \<Rightarrow> (F_finished(r0,k,r,kvs,stk))))
)"


(* general recursive find ------------------------------------- *)

type_synonym 'a trace = "nat \<Rightarrow> 'a"

fun find :: "fs \<Rightarrow> (fs MM) trace" where
"find fs n = (
  case n of 0 \<Rightarrow> (find_step fs)
  | Suc n \<Rightarrow> ( (find fs n) |>bind find_step)
)
"    

(* and prove for code extraction... but we really want the first place (if any) that we get F_finished FIXME express in terms of leaf, and rewrite using "current" state to next state *)

(*
definition find_def_2 :: bool where
"find_def_2 = (! fs n. find fs n = (if n=0 then return (Some fs) else 
  step fs|>bind (% fs'. case fs' of None \<Rightarrow> return None | Some fs' \<Rightarrow> find fs' (n-1))))"
*)



(* wellformedness --------------------------------------------------------- *)

(* FIXME is it better to map into a tree stack, and have the code above for tree stack transitions? 

ie a refinement proof? probably it is
*)


(* t0 is the tree we expect *)
definition wellformed_find_state :: "store \<Rightarrow> tree \<Rightarrow> find_state => bool" where
"wellformed_find_state s t0 fs = assert_true' (
  let r_to_t = r_to_t s in
  case fs of 
  F_finished (r0,k,r,kvs,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    (t_fo,t_stk) = (Leaf(kvs),stk|>stack_map r_to_t))
  | F_down (r0,k,r,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    (t_fo,t_stk) = (r_to_t r,stk|>stack_map r_to_t)
  )
)"


(* find_trans ----------------------------------------- *)

definition find_trans :: "(store * fs) trans_t" where
"find_trans = { ((s,fs),(s',fs')). (find_step fs s = (s',Ok fs')) }"


(* lemmas ------------------------------------------- *)

(* wf_fts is invariant *)
definition invariant_lem :: "bool" where
"invariant_lem = (
  ! P s t0. 
  ((% s_fs. let (_,fs) =  s_fs in wellformed_find_state s t0 fs) = P) \<longrightarrow> invariant find_trans P)"


(* testing ---------------------------------------- *)

(* really wf_trans is trivial, but for testing we check some obvious properties *)

(* FIXME probably not worth doing *)
definition wf_trans :: "(store * fs) \<Rightarrow> (store * fs) \<Rightarrow> bool" where
"wf_trans s1 s2 = assert_true' (
  let (s1,fs1) = s1 in
  let (s2,fs2) = s2 in
  (* FIXME dont want to force equality check of the store (s2=s1) & *)
  (case (fs1,fs2) of
  (F_down(r0,k,r,stk),F_down(r0',k',r',stk')) \<Rightarrow> (List.length stk' = 1+List.length stk)
  | (F_down(_),F_finished(_)) \<Rightarrow> True
  | _ \<Rightarrow> False)
)"


end
