(** Isa_btree_test

This package contains the test code for {!Isa_btree}.

We specialize to key,value = int,int.

Then we construct leaf node and frame impls in
   {!Test_leaf_node_frame_impls}. The function
   {!Test_leaf_node_frame_impls.make_btree_ops} keeps monad_ops, cs and
   store_ops free.

Module {!Test_monad} fixes the monad_ops using a state-passing monad.

The store ops are provided by {!Test_store}.

{!Test_util} is not very interesting.

{!Test_exhaustive} is deprecated. It attempted to use a depth-first
   search exploration of the state space. Exhaustive testing was found
   to be a better choice.

{!Test_exhaustive_2} is a "main" module, which reads a config file
   (currently expected at "test_exhaustive_2.json"), and runs an
   exhaustive testing routine.

{!Test_delete} contains unit tests for specific delete cases that were
   found to be incorrect in the past.

{!Test_insert_all} contains some tests for insert_many and insert_all.

{!Test_sequential_insert} repeatedly calls insert (not insert_many or
   all). Used for assessing the improvement in performance afforded by
   insert_many.

*)
