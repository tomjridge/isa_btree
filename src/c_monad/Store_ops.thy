theory Store_ops
imports Monad
begin

(*
(* FIXME why is store_ops here?  FIXME eliminate in favour of a tuple *)
record ('k,'v,'r,'t) store_ops =
  store_read :: "('r \<Rightarrow> (('k,'v,'r) dnode,'t) MM)"
  store_alloc :: "(('k,'v,'r) dnode \<Rightarrow> ('r,'t) MM)"
  store_free :: "('r list \<Rightarrow> (unit,'t) MM)"
*)

(* FIXME pass store_ops explicitly ? *)

type_synonym ('k,'v,'r,'t) store_ops = "
  ('r \<Rightarrow> (('k,'v,'r) dnode,'t) MM) *
  (('k,'v,'r) dnode \<Rightarrow> ('r,'t) MM) *
  ('r list \<Rightarrow> (unit,'t) MM)"

definition wf_store_ops :: "('k,'v,'r,'t) store_ops \<Rightarrow> bool" where 
"wf_store_ops s = True"

definition store_read :: "('k,'v,'r,'t) store_ops => ('r \<Rightarrow> (('k,'v,'r) dnode,'t) MM)" where
"store_read raf = (let (r,a,f) = raf in r)"

definition store_alloc :: "('k,'v,'r,'t) store_ops => (('k,'v,'r) dnode \<Rightarrow> ('r,'t) MM)" where
"store_alloc raf = (let (r,a,f) = raf in a)"

definition store_free :: "('k,'v,'r,'t) store_ops =>  ('r list \<Rightarrow> (unit,'t) MM)" where
"store_free raf = (let (r,a,f) = raf in f)"


end