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
* `Key_value` - various definitions relating to keys and orders on
  keys; includes `check_keys`, `kvs_insert`, `search_key_to_index`,
  `split_ks_rs`, `split_leaf` and `split_node`
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

* `Find.thy` - definition of `find`; `find` is used by the other
  operations
* `Insert.thy` - insert a `(key,value)` pair
* `Delete.thy` - delete a key from the B-tree
* `Insert_many.thy` - more efficient than calling `insert` repeatedly
* `Leaf_stream.thy` - it is often useful to be able to iterate over
  the leafs in a B-tree (for example, to find the list of key-value
  pairs in the tree); the leaf stream is a functional alternative to
  the usual leaf pointers found in imperative implementations


# Basics // ------------------------------------------------------------

FIXMEt0k0

## Basics: maps, keys, values, total orders // -------------------------

A B-tree is an implementation of a map (from keys to values),
specialized for block storage.

A map is (traditionally) a set of pairs ${}(k,v)$, where $k$ is the key
and $v$ the associated value. At most one value is associated to each
key. In computer science, maps are finite functions (the set of pairs
is finite). Maps may be written, for example, as $((k_1 -> v_1, k_2 -> v_2, \ldots))$.

Maps support 3 basic operations: find, insert and delete.

\newcommand{\find}{\textit{\textsf{find}}}
\newcommand{\ins}{\textit{\textsf{insert}}}
\newcommand{\delete}{\textit{\textsf{delete}}}

- $\find\ k\ m$ : return the value (if any) associated to k in map m
- $\ins\ k\ v\ m$ : add (k,v) to m, returning the updated map
- $\delete\ k\ m$ : remove all pairs of the form ${}(k,v)$ from m (there is
  at most one!) and return
  the resulting map (which may not have changed if there was no pair
  ${}(k,v)$ in $m$)

*Note:* In order to implement maps, keys are typically required to be totally
ordered.

*Definition:* a relation $\le$ on a set $S$ is a total order iff it is a
partial order which satisfies the trichotomy law: for all $a\in S,\ \ 
b\in S$ we have $a \le b\ \textit{or}\ b \le a$.  The name of the law arises from
the version of the axiom for the strictly-less operation: $a < b\
\lor\ a=b\ \lor\  b < a$. 

Typical examples of total orders are: natural numbers, integers,
reals, strings (ordered lexicographically).


## Basics: search trees as implementations of maps // ------------------

A B-tree is a form of search tree\footnote{See
\url{https://en.wikipedia.org/wiki/Search_tree}}.  Search trees are
well-known, and often covered in basic computer science courses. The
search tree datastructure is most often used to implement a map. An
example search tree is:

\includegraphics{pics/btree_example.dot.pdf}

Given a key of interest, say $k$, a search tree provides an efficient
way to navigate to the leaf that possibly contains $k$ and it's
associated value $v$.


In the example tree, keys are integers. *Leaves* contain lists of
(key,value) pairs, but values have been omitted and only the keys are
shown. However, it is worth remembering that for every key (such as 5) in a
leaf, there is an associated value (say, $v_5$). Leaves cannot be
empty, and contain a given key at most once.

*Notation:* we write leaves as ${}(k_0, v_0), (k_1, v_1), \ldots$. When the
values do not play an "active" role, we omit them and simply write
$k_0, k_1, \ldots$.

*Note:* the set of ${}(k,v)$ pairs in the leaves of a search tree constitute a
map. 

A *node* consists of (typically pointers to) children separated by
keys. The keys are in increasing order: $k_0 < k_1 < \ldots$. Again, nodes
cannot be empty, and a usual restriction is that a node must contain at
least one key and two children.

*Example:* find TODO

*Notation:* We rarely deal with nodes in isolation. Instead we depict
a tree $t$ as: $\t0tn()$. Here $t_i$ is the ith child of
$t$, and each child is separated from the next by a key. The vertical
alignment emphasizes the distinction between keys and children, but
this is only suggestive, and we also write nodes as $t_0, k_0, \ldots$.


//  FIXME use this {{{t0tn}}} notation throughout
//  
//  Sometimes we use a tabular format:
//  
//  |    | k0 |    | k1 |    | ... |        | k(n-1) |      |
//  | t0 |    | t1 |    | t2 | ... | t(n-1) |        | t(n) |
//  

*Definition:* A search tree $t$ satisfies the following property: for EVERY node
$t = t_0,k_0,\ldots$ we have 
$k_{i-1} \le keys(t_i) < k_i$, where $keys(t)$ denotes all the keys in
the (nodes and leaves of) tree $t$. If $i=0$ we may take $k_{-1}$ to
be negative infinity, so that $keys(t_0) < k_0$. Similarly for $i=n$ we may take $k_{n}$ to
be positive infinity, so that $k_{n-1} \le keys(t_n)$. 

The fact that this property holds for every node means that every
subtree of a search tree is itself a search tree.

An alternative way to phrase the above: the keys $k_0,\ldots,k_{n-1}$
partition the space of keys into $K_0,K_1,\ldots,K_n$ such that $K_0 <
k_0 \le K_1 < k_1 \ldots k_{n-1} \le K_n$. A "partition" means that
the $K_i$ are disjoint and the union of $K_i$ is the set of all keys.  This guarantees that for
any key $k$ there is a unique $i$ such that $k \in K_i$.

For a particular search tree $t = t_0,k_0,\ldots$ we have $keys(t_i)
\subseteq K_i$. This allows us to state things more succinctly than
might otherwise be the case. For example, rather than saying (find $i$
such that $k_{i-1} \le k < k_i$), we can say instead (find $i$ such
that 
$k \in K_i$). Note that this is merely a shorthand, and certainly any
implementation must not actually compute $K_i$, since such a set may
be non-finite (e.g. if keys are strings, or reals).

Informally the *algorithm for "find"* is as follows: given search key
$k$, and initial search tree $t$, starting at the root node...

- for current non-leaf node, find $i$ such that $k \in K_i$ (i.e., $k_{i-1} \le k < k_i$), with subtree $t_i$
  (this is the only subtree that can contain $k$) and descend to child $t_i$
- stop when you have reached a leaf; return the value (if any) associated with
  $k$ in the leaf


Given $k$ and $t$, the find algorithm returns the value $v$
associated with $k$ in $t$ (if any). Clearly the algorithm returns $v$
iff ${}(k,v)$ is in the map corresponding to $t$. We might call this map
$m(t)$ or $m_t$. 

Then there are two versions of find, $\find{}_m\ k\ m$
which operates on maps, and $\find{}_t\ k\ t$ which operates on search
trees. Normally we omit the subscripts, since the particular version
of find is determined by the type of the last argument (map or tree).

So, the algorithm above implements $\find\ k\ t$ for the tree $t$, and this
function "behaves the same as" $\find\ k\ m_t$ in the sense that $\find\
k\ t = \find\ k\ m_t$. In later sections we treat more complicated
variants of the "behaves the same as" concept.

*Lemma:* $\find{}_t$ is correct, in the sense that: for all $k,t$ we have $\find\ k\ t =
\find\ k\ m_t$.

*Proof:* We show $\forall\ t\ k.\ \find\ k\ t =
\find\ k\ m_t$ by induction on the size of $t$. The leaf case is
trivial. For the non-leaf case, we have $t=t_0,k_0,\ldots$. There is a
unique $i$ such that $k \in K_i$. Consider $t_i$. Apply induction
hypothesis to obtain $\find\ k\ t_i = \find\ k\ m_{t_i}$. Moreover
$\ldots = \find\ k\ m_t$ since $m_t$ is the disjoint union of
$m_{t_j}$, and $m_{t_i}$ is the only map that may contain $k$. Finally $\find\ k\ t = \find{}_t\ k\ t_i$ by definition of $\find{}_t$.


---

NOTE a B-tree is a type of balanced search tree

NOTE various kinds of B-tree in literature; ours is closest to Rodeh



## Basics: state transition systems and invariants

A state transition system is a way to model a system whose state
changes over time. 

*Definition:* Formally, a state transition system is a pair
consisting of a set of states $S$, and a set of pairs $T$. Each pair
${}(s,s') \in T$ is such that $s \in S$ and $s' \in S$. Additionally
there is often a third component $S_{init}$ of initial (starting)
states. 

*Notation:* We use the notation $s\ T\ s'$ to mean ${}(s,s') \in T$.

*Definition:* A transition sequence (or T-sequence) is just a (finite or
infinite) sequence $s_0,s_1,\ldots$ where for each pair of states
$s_i,s_{i+1}$, the pair is a valid transition $s\ T\ s'$.

*Definition:* A trace is a T-sequence where the initial state $s_0$ is drawn from $S_{init}$.

NOT TRUE A state transition system (with or without $S_{init}$) is isomorphic
to a set of traces. FIXME

*Definition:* A property $P$ is, for our purposes, just a subset of $S$, that is, a
property $P$ picks out elements of $S$ that "satisfy the
property". 

$P(s)$ is true iff $s \in P$. Alternatively we may say that
$P$ holds of $s$. The notation $P(s)$ is often used to emphasize that
$P$ is a property of states $s$.

*Definition:* A T-invariant is a property $P$ such that the following holds: if
$P(s)$ and $s\ T\ s'$ then $P(s')$. Clearly an invariant is relative
to the set of transitions $T$. The use of the word "T-invariant"
emphasizes the role of $T$. This is useful when we work
with state transition systems ${}(S',T')$ that are restrictions of some
${}(S,T)$, when we can distinguish a T-invariant from a T'-invariant
(any T-invariant is a T'-invariant!). Note that this definition is a
definition on T-transitions/T-sequences, NOT on traces: the initial state is
unconstrained.

*Definition:* A trace-invariant of a state transition system ${}(S,T)$ is a property $P(s)$
that is a T-invariant and which holds for all initial states.

*Definition:* A state is reachable when there is some trace that includes the state.

*Definition:* An invariant of a state transition system ${}(S,T)$ is a property $P(s)$
that holds for all reachable states. 

Essentially, showing that some property is an invariant of a state
transition system usually involves showing that the property is a
trace-invariant, which in turn requires showing that the property is a 
T-invariant. However, it is often useful to separate these concepts
(at least, the concept of T-invariant from the other two).



## Basics: traversing a tree, context and focus

\includegraphics{pics/focus_part.pdf}

Tree algorithms typically involve traversing the tree from top to
bottom. The algorithm starts at the root of the tree (labelled (a)
above), and descends to a child (b) until finally reaching
a leaf (c).

We may view the algorithm as operating on the "root
node", and at each step we move to a child node. This is the "graph"
view of an algorithm. It emphasizes that nodes are considered in
isolation, and pointers are followed to reach other nodes.

Alternatively, we may view the algorithm initially operating on
the whole tree, and at each step changing focus to operate on a
subtree. This is the "algebraic datatype" view of an algorithm. It
avoids mentioning pointers, which simplifies many things (but clearly
pointers are relevant at some level!).

In this work, we emphasize the "algebraic" viewpoint. Of course, when
dealing with real blocks and pointers between blocks we are forced to
consider the "graph" view.

At (a), the focus is on the entire tree. The context, which is the
part of the tree that we do not focus on, is empty. 

At (b), we focus on the "light grey" subtree (containing 15,
12, AND 19). The context is "the rest of the tree", i.e., all
nodes and edges not in the light-grey subtree. The context is like the
whole tree, but with a "gap" or "hole" where the subtree (b) should be. We will
consider how to model this hole in later sections.

At (c), we focus on the dark-grey subtree containing a single leaf
node. The context is "the rest of the tree", that is the whole
tree but with a gap or hole where the leaf should be.

Informally, a focus is the subtree we are currently dealing with, and
the context is the remaining part of the tree which we use to assemble
the final result.


*Notation:* The syntax $t[s]$ is the tree t with subtree $s$ as focus. When we
want to refer to the context we write $t[\ ]$. When we want to
emphasize the location of the focus $s$ in the original tree $t$ we
write $t[s]_p$, where $p$ is the path from the root of $t$ to the focus $s$.

*Note:* For find, the focus is always a subtree; for insert and delete, we
generalize to allow the focus to be eg two trees (because inserting a
kv in a subtree may cause the subtree to split)

# FIXME../btree_pics/IMG_20170616_150443157.jpg



## Basics: refinement, small step vs big step

"Mathematical" functions map an argument to a result. There is no
notion of the "steps" of the function, since the underlying model of a
function is as a
set of pairs.

In computer science, however, programs typically do take several
steps to execute. The distinction is important when the step-based
nature of the computation can be observed. Concurrency is one way that
the internal workings of an algorithm may be observed by another
process. However, even for a single process, we may wish to model the
program's steps explicitly. In the case of a B-tree, disk reads and
writes can be observed by other processes, but even for a single
process we want to argue that, say, the algorithm behaves correctly in
the presence of host failure (which may occur at any point during the
program's execution). A host failure causes the whole system
to enter a "halt" state, which it exits when the user restarts the
host (say). Since the failure can occur at any point, the essential
step-based nature of any programs that use the disk is observable
(some reads and writes may have happened before the host failed, but
not necessarily all that would have occurred in a full run of the
program without host failure).

So far, we have considered the "find" operation executing on a map and
on a tree:

\includegraphics{./pics/tikz_big_step.pdf}

// # #+BEGIN_SRC
// # m_t,find k m_t ---> m_t,v
// # ^                   ^
// # |                   |
// # t,find k t     ---> t,v
// # #+END_SRC

In this diagram, we show (bottom left) the tree $t$, and the operation
$\find\ k\ t$ evaluating to $t$ (unchanged) and the result $v$
(say). The top of the diagram shows the equivalent "mathematical
function" evaluating on the map $m_t$. The vertical arrows represent
the relation between $t$ and $m_t$.

In this diagram, both versions of $\find$ take a single step to
evalute. We now wish to address a more complicated scenario where the
implementation of $\find$ on a search tree takes multiple steps. Each
of these steps nominally corresponds to at most one disk operation, so
that we properly capture the fact that disk accesses (or, more
properly, requests for disk accesses) occur in sequence
over a period of time.

First of all, we suppress (for the sake of clarity) the arguments $t$
and $m_t$:

~~~~
m_t,find(k) ---> m_t,v
^                ^
|                |
t,find(k)   ---> t,v
~~~~



If we include multiple steps for the implementation $\find{}_t$, the
diagram now looks like this:

~~~~
m_t,find(k) -----------------------------------> m_t,v
^                                                ^
|                                                |
t,find(k) --> t[s],find(k) --> t[s'],find(k) --> t,v
~~~~

Here we have used the notation $t[s]$ to emphasize that the
implementation descends from the root of the tree to the subtree $s$,
and then to the subtree $s'$.

The sequence of steps of the implementation constitute a *refinement* of
the single step of $\find{}_m$. 

It is possible to use the formal notion of state transition system to
make the "refinement" notion precise. For the moment it suffices to
understand that an implementation is a refinement of a specification
when operations (such as find) "behave the same" given that we choose
to ignore some details of how the implementation behaves (in this
case, we choose to ignore the fact that the implementation takes many
steps whilst the specification consists of only one). 

*Note on etymology:* In the Oxford English Dictionary, one definition of
refinement is: "the improvement or clarification of something by the
making of small changes". Here we clarify HOW the find operation is
implemented. The move from a single step to multiple small steps also
recalls the essential "breaking down" and "separating out" aspects of
refining in various forms.


## B-tree definition

In this section we give the formal definition of a B-tree. 

*Definition:* B-trees are search trees which are:

- balanced (every leaf is at the same distance from the root)
- have minimum and maximum bounds on the sizes of nodes and leaves;
  individual nodes and leaves can vary in size between these bounds;
  there are four bounds: min leaf size, max leaf size, min node keys,
  max node keys; the root node may not satisfy the "minimum node keys"
  bound

A B-tree is, therefore, simply a balanced search tree with size constraints
on nodes and leaves.

The bounds on the sizes of nodes and leaves are chosen for performance
reasons, and to match the blocksize of the backing block
device. These aspects are visible at the block layer, but at the
current level what matters is that these bounds exist.

*Note on performance:* The fact that the tree is balanced, together with a reasonably chosen
minimum node size (say, half the maximum node size), guarantees
$O(log\ n)$ access to any leaf.

The use of minimum and maximum bounds, rather than a fixed size, means
that (potentially expensive) tree rebalancing occurs rarely, when
compared to, for example, a binary search tree.

*Note on root size constraints:* TODO


//  # A B-tree is a tree where nodes are of the form $t =
//  # t_0,k_0,\ldots,k_{n-1},t_n$ (usually written {{{t0tn}}}) and leaves are of the form
//  # $(k_0,v_0),(k_1,v_1),\ldots$. Keys in nodes and leaves are ordered in
//  # strictly increasing order.
//  # 
//  # Additionally the following are satisfied:
//  # 
//  # - the tree is balanced
//  # - all nodes and leaves (except possibly the root) have sizes
//  #   consistent with the min/max bounds
//  # - for a node $t=t_0,k_0,\ldots$, have $t_i \subseteq K_i$

## Overview of approach to correctness

Our approach to showing the correctness of the B-tree involves 2
refinements. 

#+attr_html: :height 200px
[[../btree_pics/map_refinement.dot.svg]]

At the top level, we have the specification, which is simply the
"mathematical" description of a map, as a set of pairs say. Each
operation "completes" in a "single step". No tree-like datastructures
are present. 

The map level is expressed at very high level of abstraction. The map
interface is exposed to users, who are already familiar with the map
 operations. However, at this level it is not possible to understand
the on-disk behaviour of the B-tree, including how it behaves when the
host fails.

At the next level, we have the B-tree modelled as an algebraic
datatype. At this level the operations take multiple steps
(correspnding to disk accesses) but there are no blocks or
pointers. It is at this level that the most interesting aspects of
B-trees can be captured, including the rebalancing required during
insert and delete operations. However, this level is still not
sufficiently detailed to capture the behaviour when the host fails.

At the lowest level, we have the B-tree modelled in full
implementation detail, with disk blocks, and pointers between
blocks. Caching and the behaviour of the underlying disk are all
important at this level. It is at this level that the behaviour under
host failure can be expressed.

Each level is a refinement of the level above. 

Our approach to correctness is to show the correctness of the datatype
level by showing a refinement from the map specification. We then show
a further refinement from the datatype to the "blocks and pointers"
version of the code.


## Framestacks: a concrete representation of context

In previous sections we discussed how the find algorithm descended a
search tree. At each step the algorithm focused on a subtree, and the
rest of the tree was dubbed the "context". We now make this notion
more precise.

#+attr_html: :height 200px
[[../btree_pics/btree_refinement.dot.svg]]

In the diagram above we start off with the notion of a position in a
tree. This is the "graph" view, where algorithms operate on single
nodes in a tree and follow pointers to child nodes. For concreteness,
a position or path in a tree might be the sequence of child indexes to
reach a particular node. Thus $0,1$ represents the node that can be
found by following the 0th child from the root, and then following the
1th child from that node (indexing from 0).

For the "datatype" view, it is more natural to identify a particular
position in a tree with the subtree at that position. Then we need
some way to formalize the context of the "rest of the tree". We could,
as above, maintain the original tree and a path to the "current"
subtree. However, we choose to develop a different notion of context
based on framestacks. The reason is that we need to implement
algorithms on the context, and these algorithms are more easily
expressed using framestacks.

The lowest level in the diagram involves reifying the notion of "tree
context" as a concrete datastructure called a framestack.

*Definition:* a frame is a node with a "missing" child; for a node
$t=t_0,k_0,\ldots$, a frame is just a pair
$(t_0,k_0,\ldots,k_{i-1}),(k_i,t_{i+1},\ldots)$. Compared to the
original node, the child $t_i$ is missing. 
  
Example TODO

*Notation:* a frame corresponding to a node $t$ with a missing child
$t_i$ may be written $t/t_i$ or $t[\ ]_i$. An alternative notation is {{{ctxt}}}.
Sometimes we use the alternative notation $t=\ldots,[\ ],\ldots$, or the
tabular form when we want to emphasize the surrounding keys:

| ... | k |     | k' | ... |
| ... |   | [ ] |    | ... |


*Definition:* a framestack is a list of frames $f_n,\ldots,f_0$. The
frame $f_0$ corresponds to the root node, and the frame $f_n$
corresponds to the parent node of the current subtree.

Example TODO

Clearly it is possible to reconstruct a tree given a context and a focus.

*Definition:* a (tree-)context is a framestack.

Informally, a *focus* is the part of some subtree that can be combined
with a context to give the original tree. However, it is often useful
to allow the focus to contain not only a fragment of a tree, or a
subtree, but also additional data.

FIXME define operation to combine a tree and a context





# Main definitions

## B-tree

We start with a simple definition of the algebraic datatype for a
(key,value) tree:

FIXMEisainput(Tree.thy/bc-bc)

Nodes consist of keys and subtrees. There is always one more subtree
than there are keys. A node may be written as 



A B-tree is a balanced tree, with size constraints on the nodes and
leaves. In addition, given a key of interest, the keys in the nodes
can be used when descending the tree in order to locate the
corresponding leaf.

## Frames and stores 

A store is a slightly abstracted view of a disk. The underlying model
of a disk is a map from block id to block. A store is a map from block
id to frame. A frame represents a single node (or leaf), with pointers
(block ids) to child nodes.


## Tree stack

A tree stack is a way to represent a "position in a tree". It consists
of a sequence of frames, starting at the root of the tree, and ending
in a subtree called the "focus". The frames represent "the rest of the
tree" excluding the focus.

Example



# ----------------------------------------------------------------------

# Tree stacks
