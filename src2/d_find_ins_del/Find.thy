theory Find 
imports "$SRC/b_store_monad/Store" "$SRC/c_tree_tstack/Tree_stack"
begin

(* find ------------------------------------------------------------------------- *)

type_synonym 'k stk = "('k,Frame.r) stack"


datatype ('k,'v) find_state = 
  F_down "r*'k*r*'k stk"  (* root, search key, lower and upper bound for r *) 
  | F_finished "r*'k*r*('k*'v)list*'k stk"

type_synonym 'k d = "r*'k*r*'k stk"
  
type_synonym 'k fo = "'k*r"  (* focus *)
  
type_synonym ('k,'v) f_finished = "r*'k*r*('k*'v)list*'k stk"

type_synonym ('k,'v) fs = "('k,'v) find_state"
  
definition dest_f_finished :: "('k,'v) fs \<Rightarrow> ('k,'v) f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk)  
)"

definition mk_find_state :: "'k \<Rightarrow> r \<Rightarrow> ('k,'v) find_state" where
"mk_find_state k r = F_down(r,k,r,[])"

record ('k,'v) ctxt = 
  dot_s :: "('k,'v) store"
  dot_ord :: "'k ord"

(* FIXME maybe want to store ks,rs as a list of (k,r), with the invariant that the last k is +inf *)

definition find_step :: "('k,'v) ctxt \<Rightarrow> ('k,'v) fs \<Rightarrow> ('k,'v) fs MM" where
"find_step ctxt fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(r0,k,r,stk) \<Rightarrow> (
    store_read (ctxt|>dot_s) r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let (stk',r') = add_new_stk_frame (ctxt|>dot_ord) k (ks,rs) stk in
        F_down(r0,k,r',stk')
      )
      | Leaf_frame kvs \<Rightarrow> (F_finished(r0,k,r,kvs,stk))))
)"


(* general recursive find ------------------------------------- *)

(*
type_synonym 'a trace = "nat \<Rightarrow> 'a"

fun find :: "fs \<Rightarrow> (fs SM_t) trace" where
"find fs n = (
  case n of 0 \<Rightarrow> (find_step fs)
  | Suc n \<Rightarrow> ( (find fs n) |>bind find_step)
)
"    

*)

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

(* mapping a block ref to a tree ----------------  *)

type_synonym ('k,'v) r2t = "(Frame.r \<Rightarrow> ('k,'v) Frame.t)"

fun r_to_t' :: "('k,'v) r2t \<Rightarrow> nat \<Rightarrow> Frame.r \<Rightarrow> ('k,'v) tree option" where
"r_to_t' s n r = (
  case n of 
  0 \<Rightarrow> None
  | Suc n \<Rightarrow> (
    (s r) |> (% frm. 
      case frm of
      Node_frame(ks,rs) \<Rightarrow> (
        let ts = List.map (r_to_t' s n) rs in
        case (! t. (t : set ts \<longrightarrow> (t \<noteq> None))) of
        True \<Rightarrow> Some(Node(ks,ts|>List.map dest_Some))
        | False \<Rightarrow> None)
      | Leaf_frame(kvs) \<Rightarrow> Some(Leaf(kvs)))))"

(*
definition r_to_t :: "('k,'v)r2t \<Rightarrow> Frame.r \<Rightarrow> ('k,'v)tree option" where 
"r_to_t s r = r_to_t' s 1000 r" (* FIXME only for proof *)
*)

definition r_stk_to_rs :: "r stk \<Rightarrow> r list" where 
"r_stk_to_rs xs = (xs|>List.map f_t)"

(* not used? 
definition r_frame_to_t_frame :: "('k,'v)r2t \<Rightarrow> ('k,'v) Frame.t \<Rightarrow> ('k,'v)tree Frame.t" where
"r_frame_to_t_frame s = frame_map (r_to_t s)"
*)



(* t0 is the tree we expect *)
(* FIXME this is a bit horrible because of the option type *)
definition wellformed_find_state :: "'k ord \<Rightarrow> ('k,'v)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> ('k,'v)find_state \<Rightarrow> bool" where
"wellformed_find_state ord s t0 fs = assert_true' (
  let r_to_t :: Frame.r \<Rightarrow> ('k,'v) tree option = r_to_t' s (height t0) in
  let rstk2tstk = (% rstk. rstk |> stack_map r_to_t) in
  case fs of 
  F_finished (r0,k,r,kvs,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack ord k t0 (List.length stk) in
    let b1 = (t_fo = Leaf(kvs)) in
    (* we want t_stk to correspond to the r_stk *)
    let b2 = (
      let ts1 = t_stk |> stack_map Some in
      let ts2 = rstk2tstk stk in
      ts1 = ts2
    )
    in
    b1&b2)
  | F_down (r0,k,r,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack ord k t0 (List.length stk) in
    let b1 = (Some t_fo = r_to_t r) in
    let b2 = (
      let ts1 = t_stk |> stack_map Some in
      let ts2 = rstk2tstk stk in
      ts1 = ts2)
    in
    b1 & b2
  )
)"


(* find_trans ----------------------------------------- *)

(*
definition find_trans :: "(store * fs) trans_t" where
"find_trans = { ((s,fs),(s',fs')). ( s|>(find_step fs|>dest_M) = (s',Ok fs')) }"
*)

(* lemmas ------------------------------------------- *)

(* wf_fts is invariant *)
(*
definition invariant_lem :: "bool" where
"invariant_lem = (
  ! P s t0. 
  ((% s_fs. let (_,fs) =  s_fs in wellformed_find_state s t0 fs) = P) \<longrightarrow> invariant find_trans P)"
*)

(* testing ---------------------------------------- *)

(* really wf_trans is trivial, but for testing we check some obvious properties *)

(* FIXME probably not worth doing *)
definition wf_trans :: "(('k,'v)store * ('k,'v)fs) \<Rightarrow> (('k,'v)store * ('k,'v)fs) \<Rightarrow> bool" where
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
