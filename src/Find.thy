theory Find 
imports Tree_stack Frame Monad (* FIXME for sktoi; move to kv *)
begin

type_synonym stk = "r stk"

datatype find_state = 
  F_down "k*r*stk"  (* search key, lower and upper bound for r *) 
  | F_finished "k*r*kvs*stk"

type_synonym d = "k*r*stk"
  
type_synonym fo = "k*r"  (* focus *)
  
type_synonym f_finished = "k*r*kvs*stk"

type_synonym fs = find_state
  
definition dest_f_finished :: "find_state \<Rightarrow> f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (k,r,kvs,stk) \<Rightarrow> Some(k,r,kvs,stk)  
)"

(* FIXME maybe want to store ks,rs as a list of (k,r), with the invariant that the last k is +inf *)

definition find_step :: "fs \<Rightarrow> fs MM" where
"find_step fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(k,r,stk) \<Rightarrow> (
    page_ref_to_frame r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let (stk',r') = add_new_stk_frame k (ks,rs) stk in
        F_down(k,r',stk')
      )
      | Leaf_frame kvs \<Rightarrow> (F_finished(k,r,kvs,stk))))
)"


(* general recursive find ------------------------------------- *)

type_synonym 'a trace = "nat \<Rightarrow> 'a"

function find :: "fs \<Rightarrow> (fs MM) trace" where
"find fs n = (
  case n of 0 \<Rightarrow> (find_step fs)
  | Suc n \<Rightarrow> ( (find fs n) |>bind find_step)
)
"    
by auto

(* and prove for code extraction... but we really want the first place (if any) that we get F_finished FIXME express in terms of leaf, and rewrite using "current" state to next state *)

(*
definition find_def_2 :: bool where
"find_def_2 = (! fs n. find fs n = (if n=0 then return (Some fs) else 
  step fs|>bind (% fs'. case fs' of None \<Rightarrow> return None | Some fs' \<Rightarrow> find fs' (n-1))))"
*)



(* wellformedness --------------------------------------------------------- *)

(* FIXME seems to be a tension between "this state results from a step from some other wf state; and 
giving the properties explicitly; presumably we should actually give the properties since the
other is a given *)

(* FIXME we don't need assert_true to take an arg now - we store the entire state anyway *)


(* FIXME isn't wellformedness just that when we reconstitute we have a wellformed tree? but when we ascend, we need to know that we can substitute the new focus in because
we haven't got the tree to compare with; rather, we have a tree with a funny hole *)


(* FIXME we should definitely convert stack to 'a stack *)

definition wellformed_find_state :: "store \<Rightarrow> tree \<Rightarrow> find_state => bool" where
"wellformed_find_state s t fs = assert_true (t,fs) (
  case fs of 
  F_finished (k,r,kvs,stk) \<Rightarrow> (wellformed_stk k t (r_to_t s) stk & (page_ref_to_frame r s|>snd = Ok(Leaf_frame kvs)))
  | F_down (k,r,stk) \<Rightarrow> (
    wellformed_stk k t (r_to_t s) stk & 
    (case stk of [] \<Rightarrow> True | f#_ \<Rightarrow> f|>f_t = r)
  )
)"

end
