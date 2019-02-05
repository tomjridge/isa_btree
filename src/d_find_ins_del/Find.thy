theory Find imports Post_monad "$SRC/b_pre_monad/Find_state" begin

(* find ------------------------------------------------------------- *)

definition find_step :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>  
('k,'v,'r) find_state \<Rightarrow> (('k,'v,'r) find_state,'t) MM" where
"find_step cs k_cmp store_ops = (
  let read = store_ops|>read in
  (% fs. 
  case fs of 
  F_finished _ \<Rightarrow> (failwith (STR ''find_step 1''))
  | F_down(r0,k,r,stk) \<Rightarrow> (
    read r |>fmap (% f. 
    case f of 
    Disk_node (ks,rs) \<Rightarrow> (
      let (frm,r) = make_frame k_cmp k r ks rs in      
      F_down(r0,k,r,frm#stk))
    | Disk_leaf kvs \<Rightarrow> F_finished(r0,k,r,kvs,stk)))))"

definition find_big_step :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>
('k,'v,'r) find_state \<Rightarrow> (('k,'v,'r) find_state,'t) MM" where
"find_big_step cs k_cmp store_ops = (
  let step = find_step cs k_cmp store_ops in
  (% i.
  iter_m (% i. case i of
    F_finished _ \<Rightarrow> (return None)
    | _ \<Rightarrow> (step i |> fmap Some))
    i))"

definition find :: "
constants \<Rightarrow> 
'k ord \<Rightarrow>
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>
'r \<Rightarrow> 'k \<Rightarrow> ('r * ('k*'v)s * ('k,'r)stk,'t) MM" where
"find cs k_cmp store_ops r k = (
  let s = make_initial_find_state k r in
  find_big_step cs k_cmp store_ops s |> bind (% s.
  case s of
  F_finished(r0,k,r,kvs,stk) \<Rightarrow> return (r,kvs,stk)
  | _ \<Rightarrow> failwith (STR ''find 1'')))"

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