theory Insert_state
imports Find_state
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* insert -------------------------------------------------------------------------- *)

datatype ('k,'v,'r) i12_t = I1 'r | I2 "'r*'k*'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r)i12_t"

type_synonym ('k,'v,'r) d (* down_state *) = "('k,'v,'r)fs*'v"
type_synonym ('k,'v,'r) u (* up_state *) = "('k,'v,'r)fo*('k,'r)rstk"

datatype (dead 'k,dead 'v,dead 'r) insert_state = 
  I_down "('k,'v,'r) d"
  | I_up "('k,'v,'r) u"
  | I_finished 'r

type_synonym ('k,'v,'r) ist = "('k,'v,'r) insert_state"  

definition mk_insert_state :: "'k \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r) insert_state" where
"mk_insert_state k v r = (I_down (mk_find_state k r,v))"


definition dest_i_finished :: "('k,'v,'r) ist \<Rightarrow> 'r option" where
"dest_i_finished s = (case s of I_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"

end