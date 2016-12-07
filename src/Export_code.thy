theory Export_code
imports Find Insert Delete "~~/src/HOL/Library/Code_Target_Numeral"
"~~/src/HOL/Library/Code_Char"
begin


export_code "Code_Numeral.nat_of_integer" "Code_Numeral.int_of_integer" 

(* these initial exports are to force the order of exported code mods; unfortunately isabelle can reorder when there are no dependencies *)
Constants.min_leaf_size 
Prelude.from_to
Key_value_types.key_ord
Key_value.key_lt
Tree.dest_Node
Tree_stack.dest_frame
Tree_stack.stack_to_lu_of_child
Store.Page_ref
Frame_types.Node_frame



(* key_value_types*)
key_ord

tree_to_leaves wellformed_tree

(* store *)
Store.Page_ref Store.Page Store.Store 
Store.page_ref_to_page Store.alloc

(* frame_types *)
Frame_types.Node_frame Frame_types.page_to_frame Frame_types.frame_to_page


Monad2.r_frame_to_t_frame

(* find *)
mk_find_state
dest_f_finished
find_step
wellformed_find_state 

(* insert *)
mk_insert_state
dest_i_finished
I1 I2 I_down I_up I_finished
insert_step
wellformed_insert_state

(* delete *)
mk_delete_state
dest_d_finished
D_small_leaf D_small_node D_updated_subtree D_down D_up D_finished  
Delete.delete_step
wellformed_delete_state


in OCaml file "generated/gen_btree.ml"


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