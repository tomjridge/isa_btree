theory Params
imports Key_value Frame
begin

(* a store is a map from page_ref to frame *)
typedecl page_ref
type_synonym r = page_ref
type_synonym rs = "r list"


(* fix a particular k v *)
typedecl k
typedecl v

type_synonym ks = "k list"
type_synonym kv = "k*v"
type_synonym kvs = "kv list" 


(* fix order *)
consts ord0 :: "k key_order"

(* fix constants *)
consts cs0 :: constants

type_synonym frame = "(k,v,r) Frame.t"

(* store type ----------------------- *)

typedecl store


end