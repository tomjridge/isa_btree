theory Leaf_stream_state
imports Find_state
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* leaf stream types ------------------------------------------------ *)

(* we need these exposed outside functor body in ML *)

(* abbreviate lss = leaf stream state *)
datatype ('k,'v,'r) lss = 
  LS_down "'r*('k,'r) stk" 
  | LS_leaf "('k*'v) list * ('k,'r) stk" 
  | LS_up "('k,'r) stk"
  
(* working with a F_finished find state, enumerate the leaves *)

type_synonym ('k,'v,'r) leaf_ref = "('k*'v)s*('k,'r)stk"

definition make_initial_lss :: "'r \<Rightarrow> ('k,'v,'r)lss" where
"make_initial_lss r = LS_down (r,[])"

(* detect when we are finished *)
definition lss_is_finished :: "('k,'v,'r) lss \<Rightarrow> bool" where
"lss_is_finished lss = (
  case lss of
  LS_up [] \<Rightarrow> True
  | _ \<Rightarrow> False)"

(* detect when we are at the next leaf *)
definition dest_LS_leaf :: "('k,'v,'r) lss \<Rightarrow> ('k*'v)s option" where
"dest_LS_leaf x = (
  case x of 
  LS_leaf (kvs,_) \<Rightarrow> Some kvs
  | _ \<Rightarrow> None)"

end