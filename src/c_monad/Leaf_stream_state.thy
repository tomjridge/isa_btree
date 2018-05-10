theory Leaf_stream_state
imports Find_state
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* leaf stream types ------------------------------------------------ *)

(* we need these exposed outside functor body in ML *)

datatype ('k,'v,'r) ls_state = 
  LS_down "'r*('k,'r) rstack" 
  | LS_leaf "('k*'v) list * ('k,'r) rstack" 
  | LS_up "('k,'r) rstack"
  
(* working with a F_finished find state, enumerate the leaves *)

type_synonym ('k,'v,'r) leaf_ref = "('k*'v)s*('k,'r)rstk"

type_synonym ('k,'v,'r) lss = "('k,'v,'r) ls_state"

definition mk_ls_state :: "'r \<Rightarrow> ('k,'v,'r)ls_state" where
"mk_ls_state r = LS_down (r,[])"

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
  | _ \<Rightarrow> None
)"

end