theory Insert_many_state
imports Find_state
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* like Insert, but allows to insert many keys during a single traversal to a leaf *)

datatype ('k,'v,'r) im_fo (* i_t*) = IM1 "'r*('k*'v)s" | IM2 "('r*'k*'r) * ('k*'v)s"

type_synonym ('k,'v,'r) fo = "('k,'v,'r) im_fo"

type_synonym ('k,'v,'r) d = "('k,'v,'r)fs * ('v * ('k*'v)s)"

type_synonym ('k,'v,'r) u = "('k,'v,'r)fo*('k,'r)stk"

datatype (dead 'k,dead 'v,dead 'r) imst (* i_state_t*) = 
  IM_down "('k,'v,'r)d"
  | IM_up "('k,'v,'r)u"
  | IM_finished "'r * ('k*'v)s"

definition make_initial_im_state :: "'k \<Rightarrow> 'v \<Rightarrow> ('k*'v)s \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)imst" where
"make_initial_im_state k v kvs r = (IM_down (make_initial_find_state k r,(v,kvs)))"


definition dest_im_finished :: "('k,'v,'r) imst \<Rightarrow> ('r * ('k*'v)s) option" where
"dest_im_finished s = (case s of IM_finished (r,kvs) \<Rightarrow> Some (r,kvs) | _ \<Rightarrow> None)"


end