theory Params
imports Pre_params
begin

(* for export order *)
definition dummy :: "unit" where "dummy = Pre_params.dummy"

(* fix types ---------------------------------------------------------- *)

(*typedecl page_ref*)
(* fix a particular k v *)
(*
datatype k = K nat
datatype v = K nat
typedecl world
*)



(* params ------------------------------------------------------- *)

type_synonym ('a,'t) MM = "'t \<Rightarrow> ('t * 'a res)"

datatype 'k ps0 = Ps0 "'k ord * constants"
definition dest_ps0 :: "'k ps0 \<Rightarrow> 'k ord * constants" where
"dest_ps0 ps0 = (case ps0 of Ps0 (a,b) \<Rightarrow> (a,b))"

definition cmp_k':: "'k ps0 \<Rightarrow> 'k ord" where "cmp_k' ps0 = (ps0|>dest_ps0|>fst)"
definition cs' :: "'k ps0 \<Rightarrow> constants" where "cs' ps0 = (ps0|>dest_ps0|>snd)"

(* prefer pairs to records in isa_export *)
datatype ('k,'v,'r,'t) ps1 = Ps1 "('k ps0) * 
  (* store_read *) ('r \<Rightarrow> (('k,'v,'r) frame,'t) MM) * 
  (* store_alloc *) (('k,'v,'r) frame \<Rightarrow> ('r,'t) MM) *
  (* store_free *) ('r list \<Rightarrow> (unit,'t) MM)"

definition dest_ps1 :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('k ps0) * 
  (* store_read *) ('r \<Rightarrow> (('k,'v,'r) frame,'t) MM) * 
  (* store_alloc *) (('k,'v,'r) frame \<Rightarrow> ('r,'t) MM) *
  (* store_free *) ('r list \<Rightarrow> (unit,'t) MM)" where
"dest_ps1 ps1 = (case ps1 of Ps1 ps1 \<Rightarrow> ps1)"

definition ps0' :: "('k,'v,'r,'t) ps1 \<Rightarrow> 'k ps0" where
"ps0' ps1 = (let (p,r,a,f) = dest_ps1 ps1 in p)"

definition store_read :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('r \<Rightarrow> (('k,'v,'r) frame,'t) MM)" where
"store_read ps1 = (let (p,r,a,f) = dest_ps1 ps1 in r)"

definition store_alloc :: "('k,'v,'r,'t) ps1 \<Rightarrow> (('k,'v,'r) frame \<Rightarrow> ('r,'t) MM)" where
"store_alloc ps1 = (let (p,r,a,f) = dest_ps1 ps1 in a)"

definition store_free :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('r list \<Rightarrow> (unit,'t) MM)" where
"store_free ps1 = (let (p,r,a,f) = dest_ps1 ps1 in f)"

definition cs :: "('k,'v,'r,'t) ps1 \<Rightarrow> constants" where
"cs ps1 = ps1 |> ps0' |> cs'"

definition cmp_k :: "('k,'v,'r,'t) ps1 \<Rightarrow> 'k ord" where
"cmp_k ps1 = ps1 |> ps0' |> cmp_k'"

end

