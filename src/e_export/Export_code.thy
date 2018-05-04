theory Export_code
imports 
"$SRC/d_find_ins_del/Find"
"$SRC/d_find_ins_del/Delete2"
"$SRC/d_find_ins_del/Insert"
"$SRC/d_find_ins_del/Insert_many"
"$SRC/d_find_ins_del/Leaf_stream"
Code_Numeral 
"~~/src/HOL/Library/Code_Target_Numeral"
"~~/src/HOL/Library/Code_Char"
begin


export_code "Code_Numeral.nat_of_integer" "Code_Numeral.int_of_integer" 

Util.is_Ok
Util.from_to
Util.String_error
Util.split_at_tests  (* FIXME remove tests in production *)
Util.split_at_3_tests
Util.from_to_tests

Prelude.constants_ext

Key_value.key_lt

(* FIXME remove tests in production code *)
Key_value.okl_tests
Key_value.ck_tests
Key_value.ck2_tests
Key_value.kvs_insert_tests

(* Searching_and_splitting.sk2i_tests *)

(* frame_types *)
Disk_node.Disk_node

Searching_and_splitting.dest_rsplit_node

(* tree *)
Tree.dest_Node
(* Tree_stack.stack_to_lu_of_child *)
tree_to_leaves 
wellformed_tree


(* pre_params *)
Pre_params.dummy
Pre_params.mk_r2t

(* params *)
Params.dummy
Params.Ps1
(* Params.store_ops_ext *)

Insert_state.mk_insert_state
Insert_state.dest_i_finished
Insert_state.I1 Insert_state.I2 Insert_state.I_down Insert_state.I_up Insert_state.I_finished

Insert_many_state.mk_im_state
Insert_many_state.dest_im_finished
Insert_many_state.IM1 Insert_many_state.IM_down

mk_delete_state
dest_d_finished
D_small_leaf D_small_node D_updated_subtree D_down D_up D_finished  

mk_ls_state lss_is_finished dest_LS_leaf 

(* monad *)
(* Monad.dest_MM *) Monad.dummy fmap  bind

(* store *) 
Store_ops.store_alloc store_read store_free

(* find *)
mk_find_state
dest_f_finished
find_step
wellformed_find_state 

(* insert *)
Insert.insert_step
Insert.wellformed_insert_state

(* insert_many *)
Insert_many.insert_step


(* delete2 *)
Delete2.delete_step
wellformed_delete_state

(* leaf_stream *)
lss_step


in OCaml file "/tmp/isa_export.ml"


(*

*)


(* tree stack versions







Tree_stack.dest_core

key_ord

tree_to_leaves wellformed_tree

(* find *)
mk_fts_state step_fts dest_fts_state 
  wellformed_fts wf_fts_trans Find_tree_stack.focus_to_leaves

(* insert *)
Inserting_one Inserting_two
Its_down Its_up
mk_its_state step_its dest_its_state  
  wellformed_its_state wf_its_trans Insert_tree_stack.focus_to_leaves
 
(* delete *)
D_small_leaf D_small_node D_updated_subtree
Dts_down Dts_up Dts_finished  
mk_dts_state step_dts dest_dts_state
  wellformed_dts_state wf_dts_trans Delete_tree_stack.focus_to_leaves

  *)



(*
print_codesetup

print_codeproc
*)
end