\title(Isabelle/HOL formalization of the B-tree datastructure)
\author(Tom Ridge)
\date(2017-12-01)

# Introduction


## Other documents

* B-tree informal documentation - FIXME
* OCaml library `tjr_btree`


# Overview of the formalization

## Preliminaries

* `Util.thy` - various utility definitions, including `failwith`,
  `assert_true` etc.
* `Prelude.thy` - Min and max size constants for nodes and leaves;
  datatype for small node or leaf; some basic transition system
  definitions.
* `Key_value` - various definitions relating to keys and orders on keys; includes `check_keys`, `kvs_insert`, `search_key_to_index`, `split_ks_rs`, `split_leaf` and `split_node`
* `Pre.thy` - depends on all the other theories, so subsequent theories
  need only import `Pre`


## Trees

* `Tree.thy` - definitions related to trees as an algebraic datatype;
  includes eg B-tree wellformedness properties such as `balanced`.
* `Tree_stack.thy` - definitions related to tree stacks


## Parameters

* `Pre_params.thy` - mainly `mk_r2t`, which maps an `r2f` (store
  reference to frame) to an `r2t` (store reference to tree)
* `Params.thy` - the development is parameterized by various things:
  key and value types, key order, min/max size constraints, store
  operations etc

## Store monad

* `Monad.thy` - the usual map and bind; the monad type `('a,'t)MM` is
  defined earlier in `Params.thy`

## Find, insert and delete

* `Find.thy` - defn of find; used by other operations
* `Insert.thy` - insert a `(key,value)` pair
* `Delete.thy` - delete a key from the B-tree
* `Insert_many.thy` - more efficient than calling `insert` repeatedly
* `Leaf_stream.thy` - it is often useful to be able to iterate over
  the leafs in a B-tree (for example, to find the list of key-value
  pairs in the tree); the leaf stream is a functional alternative to
  the usual leaf pointers found in imperative implementations


# Main concepts, informally

## B-tree
## Tree stack


# ----------------------------------------------------------------------

# Tree stacks
