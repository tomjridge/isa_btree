theory Monad2
imports Frame
begin

(* FIXME remove this *)


(* parameterize the pure/block implementation *)


(*
definition get_store :: "store MM" where
"get_store = (% s. (s,Ok s))"
*)

(*
definition page_ref_to_frame :: "r \<Rightarrow> pfr M_t" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r) |> dest_SM |> fmap_error se_to_e"

definition alloc :: "p \<Rightarrow> r MM" where 
"alloc p = (Store.alloc p |> dest_SM |> fmap_error (% se. Store_error se))"

definition free :: "r list \<Rightarrow> unit MM" where
"free ps = (Store.free ps |> dest_SM |> fmap_error (% se. Store_error se))"
*)

end