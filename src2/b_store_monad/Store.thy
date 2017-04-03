theory Store
imports "$SRC/a_pre/Frame" Monad
begin

type_synonym r = Prelude.r

(* store api -------------------------------------------------- *)

FIXME remove tyvars, and s2ord (since kv is now parameter)

datatype ('k,'v) store = Store "nat" (* page_ref \<Rightarrow> page" (* s *) *)

(*
definition dest_Store :: "store \<Rightarrow> page_ref \<Rightarrow> page" where
"dest_Store s r = (failwith (STR ''FIXME''))"
*)

definition "store_read" :: "('k,'v) store \<Rightarrow> r \<Rightarrow> ('k,'v) Frame.t MM" where
"store_read s r = failwith (STR ''FIXME'')"

definition "store_alloc" :: "('k,'v) store \<Rightarrow> ('k,'v) Frame.t \<Rightarrow> r MM" where
"store_alloc s frm = failwith (STR ''FIXME'')"

definition "store_free" :: "('k,'v) store \<Rightarrow> r list \<Rightarrow> unit MM" where
"store_free s rs = failwith (STR ''FIXME'')" 

definition s2c :: "('k,'v) store \<Rightarrow> constants" where
"s2c s = failwith (STR ''FIXME'')"

definition s2ord :: "('k,'v) store \<Rightarrow> ('k \<Rightarrow> 'k \<Rightarrow> int)" where
"s2ord s = failwith (STR ''FIXME'')"

(* for testing ------------------------------------------------- *)

type_synonym ('k,'v) r2f = "(r \<Rightarrow> ('k,'v) Frame.t option)"

(* throw exception if no frame for given r *)
definition "get_store" :: "('k,'v) store \<Rightarrow> ('k,'v) r2f MM" where
"get_store s = failwith (STR ''FIXME'')"

definition dest_MM :: "world \<Rightarrow> 'a MM \<Rightarrow> 'a" where
"dest_MM m w = failwith (STR ''FIXME'')"

definition store_to_r2f :: "('k,'v) store \<Rightarrow> world \<Rightarrow> ('k,'v) r2f" where
"store_to_r2f s w = get_store s |> dest_MM w"

(* btree create ------------------------------------------- *)

(* here because related to store and monad *)

datatype ('k,'v) btree = Btree nat

definition empty_btree :: "unit \<Rightarrow> ('k,'v) btree MM" where
"empty_btree _ = failwith (STR ''FIXME'')"

(*
(* empty leaf *)
  let lf = Leaf_frame([]) in
  lf |> alloc 
)
*)



end
