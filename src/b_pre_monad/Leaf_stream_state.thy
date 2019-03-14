theory Leaf_stream_state
imports Find_state
begin

(* NOTE use prefix ls *)

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* leaf stream types ------------------------------------------------ *)

(* we need these exposed outside functor body in ML *)

(* abbreviate lss = leaf stream state *)
datatype ('r,'leaf,'frame) ls_state = 
  LS_down "'r*'frame list" 
  | LS_leaf "'leaf * 'frame list" 
  | LS_up "'frame list"
  
(* working with a F_finished find state, enumerate the leaves *)

(* type_synonym ('k,'v,'r) leaf_ref = "('k*'v)s*('k,'r)stk" *)

definition make_initial_ls_state :: "'r \<Rightarrow> ('r,'leaf,'frame)ls_state" where
"make_initial_ls_state r = LS_down (r,[])"

(* detect when we are finished *)
definition ls_is_finished :: "('r,'leaf,'frame) ls_state \<Rightarrow> bool" where
"ls_is_finished lss = (
  case lss of
  LS_up [] \<Rightarrow> True
  | _ \<Rightarrow> False)"

(* detect when we are at the next leaf *)
definition dest_LS_leaf :: "('r,'leaf,'frame) ls_state \<Rightarrow> 'leaf option" where
"dest_LS_leaf x = (
  case x of 
  LS_leaf (leaf,_) \<Rightarrow> Some leaf
  | _ \<Rightarrow> None)"

end