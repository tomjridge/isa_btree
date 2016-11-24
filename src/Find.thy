theory Find 
imports Tree_stack Frame Monad (* FIXME for sktoi; move to kv *)
begin

datatype find_state_t = 
  F_down "k*k option*r*k option*stk"  (* search key, lower and upper bound for r *) 
  | F_finished "k*k option * r * k option * kvs*stk"
  
type_synonym f_finished = "k*k option*r*k option*kvs*stk"

type_synonym fs = find_state_t
  
definition dest_f_finished :: "find_state_t \<Rightarrow> f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (k,l,r,u,kvs,stk) \<Rightarrow> Some(k,l,r,u,kvs,stk)  
)"

(* FIXME maybe want to store ks,rs as a list of (k,r), with the invariant that the last k is +inf *)

definition find_step :: "fs \<Rightarrow> fs MM" where
"find_step fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(k,l,r,u,stk) \<Rightarrow> (
    page_ref_to_frame r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let i = search_key_to_index ks k in
        let (ks1,ks2) = split_at i ks in
        let (rs1,r',rs2) = split_at_3 i rs in
        let (l',u') = (
          if ks1 = [] then l else Some(List.last ks1),
          if ks2 = [] then u else Some(List.hd ks2))
        in
        F_down(k,l',r',u',(l,((ks1,rs1),(ks2,rs2)),u)#stk)
      )
      | Leaf_frame kvs \<Rightarrow> (F_finished(k,l,r,u,kvs,stk))))
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


end
