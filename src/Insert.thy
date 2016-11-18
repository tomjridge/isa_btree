theory Insert
imports Find
begin

datatype i_error = I_fe fe | I_malformed_stack string | I_se se
type_synonym ie = i_error
type_synonym e = ie

datatype i_t = I1 r | I2 "r*k*r"

type_synonym focus_t = "i_t"
type_synonym fo = focus_t

datatype i_state_t = 
  I_down "fs*v"
  | I_up "fo*stk"
type_synonym is_t = i_state_t  


type_synonym 'a M = "s \<Rightarrow> (s * ('a,e) rresult)"
(* s \<Rightarrow> (s * ['a + e] ) *) 

definition bind :: "('a \<Rightarrow> 'b M) \<Rightarrow> 'a M \<Rightarrow> 'b M" where
"bind f v = (% s. (case v s of (s1,Error x) \<Rightarrow> (s1,Error x) | (s1,Ok y) \<Rightarrow> (f y s1)))"

definition return :: "'a \<Rightarrow> 'a M" where
"return x = (% s. (s,Ok x))"

definition get_store :: "unit \<Rightarrow> s M" where
"get_store _ = (% s. (s,Ok(s)))"

definition split_leaf :: "kvs \<Rightarrow> (kvs * k * kvs)" where
"split_leaf kvs = (
  let min = min_leaf_size in
  let (l,r) = split_at min kvs in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible) in
  (l,k,r)
)"

definition split_node :: "ks_rs \<Rightarrow> (ks_rs * k * ks_rs)" where
"split_node n = (
  let (ks,rs) = n in
  let min = min_node_keys in
  let (ks1,k,ks2) = split_at_3 min ks in
  let (rs1,rs2) = split_at (min+1) rs in
  ((ks1,rs1),k,(ks2,rs2))
)"

definition i_alloc :: "p \<Rightarrow> r M" where 
"i_alloc p = (
  get_store () |>bind 
  (% s. let r = alloc s p in 
  case r of Error se \<Rightarrow> (% s1. (s1,Error (I_se  se))) | Ok y \<Rightarrow> (% s1. (s1,Ok y))) 
)"


end