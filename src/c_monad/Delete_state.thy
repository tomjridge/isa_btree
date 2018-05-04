theory Delete_state
imports Find_state
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* delete -------------------------------------------------------------------- *)

datatype ('k,'v,'r)del_t =
  D_small_leaf "('k*'v)s"
  | D_small_node "'k s * 'r s"
  | D_updated_subtree "'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r) del_t"  (* focus *)

(* dead: https://groups.google.com/forum/#!topic/fa.isabelle/hWGSgu3pSsM *)

(* D_down: r is the original pointer to root, in case we don't delete anything *)
datatype (dead 'k, dead 'v,dead 'r) delete_state = 
  D_down "('k,'v,'r) fs * 'r"  
  | D_up "('k,'v,'r) fo * ('k,'r) rstk * 'r"  (* last 'r is the root, for wellformedness check *)
  | D_finished "'r" 
  
type_synonym ('k,'v,'r)u = "('k,'v,'r)fo * ('k,'r)rstk"  
type_synonym ('k,'v,'r)d = "('k,'v,'r)find_state * 'r"

type_synonym ('k,'v,'r)dst = "('k,'v,'r) delete_state"

definition mk_delete_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)dst" where
"mk_delete_state k r = (D_down(mk_find_state k r,r))"

definition dest_d_finished :: "('k,'v,'r)dst \<Rightarrow> 'r option" where
"dest_d_finished x = (case x of D_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"




end