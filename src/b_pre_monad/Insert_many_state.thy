theory Insert_many_state
imports Find_state Insert_state
begin

(* like Insert, but allows to insert many keys during a single traversal to a leaf; FIXME perhaps we 
prefer a batch operation? *)

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"
(*
type_synonym ('k,'v,'r,'leaf,'frame) im_d = "('k,'v,'r,'leaf,'frame)d * ('k*'v)s"

type_synonym ('k,'v,'r,'frame) im_u = "('k,'v,'r,'frame)u * ('k*'v)s"
*)

type_synonym ('k,'v,'r,'leaf,'frame) im_state = "('k,'v,'r,'leaf,'frame) insert_state * ('k*'v)s"

definition make_initial_im_state :: "'r \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k*'v)s \<Rightarrow> ('k,'v,'r,'leaf,'frame)im_state" where
"make_initial_im_state r k v kvs = (
  let i = make_initial_insert_state r k v in
  (i,kvs))"

end

