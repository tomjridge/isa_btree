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
