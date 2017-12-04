theory Params
imports Pre_params
begin

(* for export order *)
definition dummy :: "unit" where "dummy = Pre_params.dummy"

(* fix types *)

(*typedecl page_ref*)
(* fix a particular k v *)
(*
datatype k = K nat
datatype v = K nat
typedecl world
*)


(* ('a,'t) MM type_synonym ------------------------------------------ *)

type_synonym ('a,'t) MM = "'t \<Rightarrow> ('t * 'a res)"



(* params ----------------------------------------------------------- *)

(* The B-tree functions are heavily parameterized; rather than pass
round many parameters individually, we package them up as follows. *)

(* FIXME ops and params are different kinds of things *)

record ('k,'v,'r,'t) store_ops =
  store_read :: "('r \<Rightarrow> (('k,'v,'r) frame,'t) MM)"
  store_alloc :: "(('k,'v,'r) frame \<Rightarrow> ('r,'t) MM)"
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





(*
definition ps1_ps0' :: "('k,'v,'r,'t) ps1 \<Rightarrow> 'k ps0" where
"ps1_ps0' ps1 = (ps1|>dest_ps1|>fst)"
*)




(*
datatype 'k ps0 = Ps0 "constants * 'k ord"

definition dest_ps0 :: "'k ps0 \<Rightarrow> constants * 'k ord" where
"dest_ps0 ps0 = (case ps0 of Ps0 (a,b) \<Rightarrow> (a,b))"

definition ps0_cs :: "'k ps0 \<Rightarrow> constants" where 
"ps0_cs ps0 = (ps0|>dest_ps0|>fst)"

definition ps0_cmp_k:: "'k ps0 \<Rightarrow> 'k ord" where 
"ps0_cmp_k ps0 = (ps0|>dest_ps0|>snd)"
*)
