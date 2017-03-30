theory Store
imports "$SRC/a_pre/Frame" Monad
begin


(* store api -------------------------------------------------- *)

datatype ('k,'v) store = Store "nat" (* page_ref \<Rightarrow> page" (* s *) *)

(*
definition dest_Store :: "store \<Rightarrow> page_ref \<Rightarrow> page" where
"dest_Store s r = (failwith (STR ''FIXME''))"
*)

definition "ptr_to_frame" :: "('k,'v) store \<Rightarrow> r \<Rightarrow> ('k,'v) Frame.t MM" where
"ptr_to_frame s r = failwith (STR ''FIXME'')"

definition "alloc" :: "('k,'v) store \<Rightarrow> ('k,'v) Frame.t \<Rightarrow> r MM" where
"alloc s frm = failwith (STR ''FIXME'')"

definition "free" :: "('k,'v) store \<Rightarrow> r list \<Rightarrow> unit MM" where
"free s rs = failwith (STR ''FIXME'')" 


end
