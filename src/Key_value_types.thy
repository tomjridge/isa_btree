theory Key_value_types
imports Prelude
begin

(* we separate the types to make it easier to functorize the generated ocaml *)

(* this makes code export easier; of course, key is abstract *)
datatype key = Private_key nat

datatype value_t = Private_value nat


type_synonym kv_t = "key * value_t"
type_synonym k = key
type_synonym v = value_t
type_synonym ks = "k list"
 

type_synonym kvs_t = "kv_t list" (* FIXME remove *)
type_synonym kvs = kvs_t



(* FIXME really an abstract parameter; this for code export *)
definition key_ord :: "key => key => int"  where (* as ocaml compare *)
"key_ord k1 k2 = failwith ''key_ord''"

(*
(* nonsense to get code export to work *)
instantiation key :: equal begin
definition equal_key :: "key \<Rightarrow> key \<Rightarrow> bool" where "equal_key = (op = )" 
instance by intro_classes (simp add: equal_key_def)
end
*)





end
