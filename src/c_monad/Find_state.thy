theory Find_state
imports Pre_monad
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"


(* we put all the types that we want "outside" the monad, but which really belong with Find, 
Insert, etc., here *)

(* we use a small-step style; we reify the state of the algorithm at every
step as the following state type *)

(* find ----------------------------------------------------------------------- *)

datatype ('k,'v,'r) find_state = 
  F_down "'r * 'k * 'r * ('k,'r) rstk"  (* root, search key, current pointer, stack *) 
  | F_finished "'r * 'k * 'r * ('k*'v)s * ('k,'r)rstk"



type_synonym ('k,'r) f_down = "'r * 'k * 'r * ('k,'r)rstk"
type_synonym ('k,'v,'r) f_finished = "'r * 'k * 'r * ('k*'v)s * ('k,'r)rstk"
type_synonym ('k,'v,'r) fs = "('k,'v,'r) find_state"

(* type_synonym ('k,'r) fo_unused = "'k*'r"  (* focus *) *)

  
  
definition dest_f_finished :: "('k,'v,'r)fs \<Rightarrow> ('k,'v,'r)f_finished option" where
"dest_f_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk) )"



definition mk_find_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)fs" where
"mk_find_state k r = F_down(r,k,r,[])"



end