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
wf_tree



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

Pre_monad.dummy

Monad.fmap 
bind
return
Monad.dummy

(* post monad ------------------------------------------------------------------------- *)

Post_monad.dummy
Post_monad.read 
wrte 
rewrite

Find.find_step

Insert.insert_step insert

Delete.delete_step delete

Leaf_stream.lss_step

Insert_many.im_step

in OCaml file "/tmp/isa_export.ml"

end