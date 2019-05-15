theory Leaf_stream_state
imports Find_state
begin

(* NOTE use prefix ls *)

(* leaf stream types ------------------------------------------------ *)

(* we need these exposed outside functor body in ML *)

datatype ('r,'leaf,'frame) leaf_stream_state = 
  LS_down "'r*'frame list"  (* FIXME r can be got from frame? not if frame list is empty; FIXME so
include the initial r in the init constructor eg LS_init 'r *)
  | LS_leaf "'leaf * 'frame list" 
  | LS_up "'frame list"
  
(* working with a F_finished find state, enumerate the leaves *)

(* type_synonym ('k,'v,'r) leaf_ref = "('k*'v)s*('k,'r)stk" *)

(* FIXME note we have to step to the next leaf at least, if the root is not a leaf *)
definition make_initial_ls_state :: "'r \<Rightarrow> ('r,'leaf,'frame)leaf_stream_state" where
"make_initial_ls_state r = LS_down (r,[])"

(* detect when we are finished *)
definition ls_is_finished :: "('r,'leaf,'frame) leaf_stream_state \<Rightarrow> bool" where
"ls_is_finished lss = (
  case lss of
  LS_up [] \<Rightarrow> True
  | _ \<Rightarrow> False)"

(* Detect when we are at the next leaf. NOTE this can be used to check if we need to step to the
next leaf when we create the initial leaf stream state. *)
definition dest_LS_leaf :: "('r,'leaf,'frame) leaf_stream_state \<Rightarrow> 'leaf option" where
"dest_LS_leaf x = (
  case x of 
  LS_leaf (leaf,_) \<Rightarrow> Some leaf
  | _ \<Rightarrow> None)"

definition dummy :: unit where "dummy = ()"

end