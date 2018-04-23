theory Params
imports Pre_params
begin

(* params ----------------------------------------------------------- *)

(* The B-tree functions are heavily parameterized; rather than pass
round many parameters individually, we package them up as follows. *)

(* FIXME? ops and params are different kinds of things *)

(* FIXME why is store_ops here? *)
record ('k,'v,'r,'t) store_ops =
  store_read :: "('r \<Rightarrow> (('k,'v,'r) dnode,'t) MM)"
  store_alloc :: "(('k,'v,'r) dnode \<Rightarrow> ('r,'t) MM)"
  store_free :: "('r list \<Rightarrow> (unit,'t) MM)"

(* FIXME pass store_ops explicitly ? *)


datatype ('k,'v,'r,'t) ps1 = Ps1 "constants * 'k ord * ('k,'v,'r,'t) store_ops"

definition dest_ps1 :: "('k,'v,'r,'t) ps1 \<Rightarrow> constants * 'k ord * ('k,'v,'r,'t) store_ops" where
"dest_ps1 ps1 = (case ps1 of Ps1 (x,y,z) \<Rightarrow> (x,y,z))"

(* NOTE dot_xxx are named after record projections *)

(* FIXME the following just lifts the ps0 projections, and is confusing *)
(* FIXME cs is normally reserved as a var *)
definition dot_constants :: "('k,'v,'r,'t) ps1 \<Rightarrow> constants" where
"dot_constants ps1 = ps1 |> dest_ps1 |> (% (x,y,z). x)"

definition dot_cmp :: "('k,'v,'r,'t) ps1 \<Rightarrow> 'k ord" where
"dot_cmp ps1 = ps1 |> dest_ps1 |> (% (x,y,z). y)"

definition dot_store_ops :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops" where
"dot_store_ops ps1 = ps1 |> dest_ps1 |> (% (x,y,z). z)"



end
