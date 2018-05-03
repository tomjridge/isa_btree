theory Store_ops
imports Monad
begin

(* FIXME why is store_ops here? *)
record ('k,'v,'r,'t) store_ops =
  store_read :: "('r \<Rightarrow> (('k,'v,'r) dnode,'t) MM)"
  store_alloc :: "(('k,'v,'r) dnode \<Rightarrow> ('r,'t) MM)"
  store_free :: "('r list \<Rightarrow> (unit,'t) MM)"

(* FIXME pass store_ops explicitly ? *)

end