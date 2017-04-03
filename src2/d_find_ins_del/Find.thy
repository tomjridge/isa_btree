theory Find 
imports "$SRC/b_store_monad/Store" "$SRC/c_tree_tstack/Tree_stack"
begin

(* btree create ------------------------------------------- *)

(* here because related to store and monad *)

datatype btree = Btree r

definition empty_btree :: "unit \<Rightarrow> btree MM" where
"empty_btree _ = (
  store_alloc (Leaf_frame[]) |> bind (% r. return (Btree r)))"




(* find ------------------------------------------------------------------------- *)


datatype find_state = 
  F_down "r * k * r * rstk"  (* root, search key, current pointer, stack *) 
  | F_finished "r * k * r * kvs * rstk"

type_synonym f_down = "r * k * r * rstk"
type_synonym f_finished = "r * k * r * kvs * rstk"
type_synonym fs = "find_state"


type_synonym fo = "k*r"  (* focus *)
  
  
definition dest_f_finished :: "fs \<Rightarrow> f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk)  
)"

definition mk_find_state :: "k \<Rightarrow> r \<Rightarrow> find_state" where
"mk_find_state k r = F_down(r,k,r,[])"

(* FIXME maybe want to store ks,rs as a list of (k,r), with the invariant that the last k is +inf *)

definition find_step :: "fs \<Rightarrow> fs MM" where
"find_step fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return fs)  (* FIXME impossible, or return none? or have a finished error? or stutter? *)
  | F_down(r0,k,r,stk) \<Rightarrow> (
    store_read r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let (stk',r') = add_new_stack_frame ord0 k (ks,rs) stk in
        F_down(r0,k,r',stk')
      )
      | Leaf_frame kvs \<Rightarrow> (F_finished(r0,k,r,kvs,stk))))
)"


(* wellformedness --------------------------------------------------------- *)

(* like to have this in a "programmatic" style; so convert a store into a map from r * nat to 
tree option, then check the r with a t , given t height *)

type_synonym r2t = "(r \<Rightarrow> kv_tree option)"

fun mk_r2t :: "r2f \<Rightarrow> nat \<Rightarrow> r2t" where
"mk_r2t s n r = (
  case n of 
  0 \<Rightarrow> None
  | Suc n \<Rightarrow> (
    case s r of
    None \<Rightarrow> None
    | Some frm \<Rightarrow> (
      case frm of
      Leaf_frame kvs \<Rightarrow> Some(Leaf(kvs))
      | Node_frame(ks,rs) \<Rightarrow> (
        let ts = List.map (mk_r2t s n) rs in
        case (None : set ts) of
        False \<Rightarrow> None
        | True \<Rightarrow> Some(Node(ks,ts|>List.map dest_Some))
      )
    )
  )
)"

definition wf_store_tree :: "store \<Rightarrow> r \<Rightarrow> kv_tree \<Rightarrow> bool" where
"wf_store_tree s r t = (
  let r2f = mk_r2f s in
  let s' = mk_r2t r2f (height t) in
  s' r = Some t
)"


(* t0 is the tree we expect *)
definition wellformed_find_state :: "store \<Rightarrow> kv_tree \<Rightarrow> find_state \<Rightarrow> bool" where
"wellformed_find_state s0 t0 fs = assert_true' (
  let n = height t0 in
  let r2f = mk_r2f s0 in
  let r2t = mk_r2t r2f n in
  (* need to check the stack and the focus *)
  let check_focus = % r t. wf_store_tree s0 r t in
  let check_stack = % rstk tstk. (tstk |> stack_map Some = rstk |> stack_map r2t) in 
  case fs of 
  F_finished (r0,k,r,kvs,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    check_focus r t_fo &
    check_stack stk t_stk)
  | F_down (r0,k,r,stk) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    check_focus r t_fo &
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
definition wf_trans :: "store * fs \<Rightarrow> store * fs \<Rightarrow> bool" where
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
