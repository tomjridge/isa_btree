theory Insert_many_state
imports Find_state Insert_state
begin

(* like Insert, but allows to insert many keys during a single traversal to a leaf *)

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

type_synonym ('k,'v,'r) dd = "('k,'v,'r)d * ('k*'v)s"

type_synonym ('k,'v,'r) uu = "('k,'v,'r)u *('k*'v)s"

type_synonym ('k,'v,'r)im_state = "('k,'v,'r) insert_state * ('k*'v)s"

type_synonym ('k,'v,'r)im = "('k,'v,'r)im_state"

definition make_initial_im_state :: "'r \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k*'v)s \<Rightarrow> ('k,'v,'r)im" where
"make_initial_im_state r k v kvs = (
  let i = make_initial_insert_state r k v in
  (i,kvs))"

end

