theory Find 
imports "Pre_find"
begin


type_synonym 'a s = "'a list"


(* find ------------------------------------------------------------- *)





definition find_step :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r)fs \<Rightarrow> (('k,'v,'r)fs,'t) MM" where
"find_step ps1 store_ops fs = (
  (* let store_ops = ps1 |> dot_store_ops in *)
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(r0,k,r,stk) \<Rightarrow> (
    (store_ops|>store_read) r |>fmap (% f. 
    case f of 
    Disk_node (ks,rs) \<Rightarrow> (
      let (stk',r') = add_new_stack_frame (ps1|>dot_cmp) k (ks,rs) stk in
      F_down(r0,k,r',stk'))
    | Disk_leaf kvs \<Rightarrow> (F_finished(r0,k,r,kvs,stk)))) )"




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