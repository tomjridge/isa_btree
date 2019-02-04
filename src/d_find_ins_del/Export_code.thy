theory Export_code
imports 
Find
Insert
Delete
Leaf_stream
Insert_many
"~~/src/HOL/Library/Code_Target_Numeral"
begin


export_code "Code_Numeral.nat_of_integer" "Code_Numeral.int_of_integer" 

is_Ok
from_to
String_error
(* split_at_tests *) (* FIXME remove tests in production *)
(* split_at_3_tests *)
from_to_tests

Key_value.key_lt
key_le
(* FIXME remove tests in production code *)
okl_tests
ck_tests
ck2_tests
kvs_insert_tests

(* Searching_and_splitting.sk2i_tests *)


Disk_node.Disk_node



Tree.dest_Node
(* Tree_stack.stack_to_lu_of_child *)
tree_to_leaves 
wellformed_tree



Find_state.make_initial_find_state
dest_F_finished
(* wellformed_find_state *)
(* Find_state.wf_trans *)



(* Insert_state.make_initial_insert_state *)
(* Insert_state.dest_i_finished *)
Insert_state.I1
I_down 


(* make_initial_delete_state *)
Delete_state.D_small_leaf
D_down
make_initial_delete_state
dest_D_finished


Insert_many_state.make_initial_im_state 


Leaf_stream_state.make_initial_lss
lss_is_finished 
dest_LS_leaf 

Monad.fmap 
bind
return

(* post monad ------------------------------------------------------------------------- *)

Post_monad.read 
wrte 
rewrite

Find.find_step

Insert.insert_step

(* Insert_many.insert_step *)

Delete.delete_step

Leaf_stream.lss_step

Insert_many.im_step


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