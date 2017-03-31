theory Find 
imports "$SRC/b_store_monad/Store" "$SRC/c_tree_tstack/Tree_stack"
begin

(* find ------------------------------------------------------------------------- *)

type_synonym 'k stk = "'k rstk"


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

(* FIXME maybe want to store ks,rs as a list of (k,r), with the invariant that the last k is +inf *)

definition find_step :: "('k,'v) store \<Rightarrow> ('k,'v) fs \<Rightarrow> ('k,'v) fs MM" where
"find_step s fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(r0,k,r,stk) \<Rightarrow> (
    store_read s r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let (stk',r') = add_new_stk_frame (s|>s2ord) k (ks,rs) stk in
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

(* slightly complicated by the fact that the tree in the store may be infinite; as an alternative we
just check whether a store is consistent with a tree *)



(* like to have this in a "programmatic" style; so convert a store into a map from r * nat to 
tree option, then check the r with a t , given t height *)

type_synonym ('k,'v) r2t = "(r \<Rightarrow> ('k,'v) tree option)"

fun frame_store_to_tree_store :: "('k,'v) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v) r2t" where
"frame_store_to_tree_store s n r = (
  case n of 
  0 \<Rightarrow> None
  | Suc n \<Rightarrow> (
    case s r of
    None \<Rightarrow> None
    | Some frm \<Rightarrow> (
      case frm of
      Leaf_frame kvs \<Rightarrow> Some(Leaf(kvs))
      | Node_frame(ks,rs) \<Rightarrow> (
        let ts = List.map (frame_store_to_tree_store s n) rs in
        case (? t. t : set ts & (t = None)) of
        False \<Rightarrow> None
        | True \<Rightarrow> Some(Node(ks,ts|>List.map dest_Some))
      )
    )
  )
)"

definition wf_store_tree :: "('k,'v) r2f \<Rightarrow> r \<Rightarrow> ('k,'v) tree \<Rightarrow> bool" where
"wf_store_tree s r t = (
  let s' = frame_store_to_tree_store s (height t) in
  s' r = Some t
)"


(* t0 is the tree we expect *)
definition wellformed_find_state :: "('k,'v) store \<Rightarrow> world \<Rightarrow> ('k,'v)tree \<Rightarrow> ('k,'v)find_state \<Rightarrow> bool" where
"wellformed_find_state str w t0 fs = assert_true' (
  let ord = str|>s2ord in
  let s = store_to_r2f str w in
  let n = height t0 in
  (* need to check the stack and the focus *)
  let check_focus = % t r. wf_store_tree s r t in
  let f = % r. frame_store_to_tree_store s n r in
  let check_stack = % rstk tstk. (tstk |> stack_map Some = rstk |> stack_map f) in 
  case fs of 
  F_finished (r0,k,r,kvs,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack ord k t0 (List.length stk) in
    check_focus t_fo r &
    check_stack stk t_stk)
  | F_down (r0,k,r,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack ord k t0 (List.length stk) in
    check_focus t_fo r &
    check_stack stk t_stk
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
