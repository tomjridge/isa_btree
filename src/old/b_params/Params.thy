theory Params
imports Pre_params
begin

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=Pre_params.dummy"

(* params ----------------------------------------------------------- *)

(* The B-tree functions are heavily parameterized; rather than pass
round many parameters individually, we package them up as follows. *)


datatype 'k ps1 = Ps1 "constants * 'k ord"

definition dest_ps1 :: "'k ps1 \<Rightarrow> constants * 'k ord" where
"dest_ps1 ps1 = (case ps1 of Ps1 (x,y) \<Rightarrow> (x,y))"

(* NOTE dot_xxx are named after record projections *)

(* FIXME the following just lifts the ps0 projections, and is confusing *)
(* FIXME cs is normally reserved as a var *)
definition dot_constants :: "'k ps1 \<Rightarrow> constants" where
"dot_constants ps1 = ps1 |> dest_ps1 |> (% (x,y). x)"

definition dot_cmp :: "'k ps1 \<Rightarrow> 'k ord" where
"dot_cmp ps1 = ps1 |> dest_ps1 |> (% (x,y). y)"

(*
definition dot_store_ops :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops" where
"dot_store_ops ps1 = ps1 |> dest_ps1 |> (% (x,y,z). z)"
*)


end