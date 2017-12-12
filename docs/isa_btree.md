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
is finite). Maps may be written, for example, as ${}(k_1 -> v_1, k_2 -> v_2, \ldots)$.

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

// # FIXME../btree_pics/IMG_20170616_150443157.jpg



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

\includegraphics{pics/map_refinement.dot.pdf}

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

\includegraphics{pics/btree_refinement.dot.pdf}

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
${}(t_0,k_0,\ldots,k_{i-1}),(k_i,t_{i+1},\ldots)$. Compared to the
original node, the child $t_i$ is missing. 
  
Example TODO

\newcommand{\ctxt}{$\ldots|^{k_{i-1}}|_{\Box}|^{k_i}|\ldots$}

*Notation:* a frame corresponding to a node $t$ with a missing child
$t_i$ may be written $t/t_i$ or $t[\ ]_i$. An alternative notation is \ctxt{}.
Sometimes we use the alternative notation $t=\ldots,[\ ],\ldots$.

// , or the
// tabular form when we want to emphasize the surrounding keys:
// 
// | ... | k |     | k' | ... |
// | ... |   | [ ] |    | ... |
// 

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



# Find


We are now in a position to describe the find implementation formally.

## Example tree

\includegraphics{pics/find1.dot.pdf}

In what follows, we use the following abbreviations:

- $t$, or $t_{(13)}$ - the whole tree
- $t_{(4,7,10)}$ the subtree rooted at $4,7,10$.
- $t_{(1,2,3)}$, the subtree rooted at $1,2,3$ (a leaf!)
- etc.

## Find: using a search key to identify a leaf 

The find operation uses a key to descend the tree, eventually
locating a leaf which possibly contains the key.

*Example:* Suppose the search key $k$ is $5$. The find operation examines the
root of $t$, determines that $k < 13$, and so descends to
$t_{(4,7,10)}$. At the next step, the find operation determines that
$4 \le k < 7$ and descends to $t_{(4,5,6)}$. At
this point the algorithm has found the relevant leaf.

The state of the algorithm comprises the search key (which is unchanged during the find
operation), the context (as a framestack),
focus (a tree), and lower and upper bounds (which play an important role
in proofs of correctness, but are not stricly necessary for
implementations). This is written as a tuple ${}(k,ctxt,t,l,u)$.

*Example:* Continuing the previous example, we can now show how the
state of the algorithm changes:


\begin{verbatim}
FIXME table formatting
| Step | Focus          | Context                       | l,u       |
|------+----------------+-------------------------------+-----------|
|    1 | $t$            | (empty)                       | -inf,+inf |
|    2 | $t_{(4,7,10)}$ | $t[\ ]_0$                     | -inf,13   |
|    3 | $t_{(4,5,6)}$  | $t_{(4,7,10)}[\ ]_1, t[\ ]_0$ | 4,7       |
\end{verbatim}


## Pseudocode for find

The main step of find can be written using pseudocode as follows:

\begin{verbatim}
// k - the search key (constant for duration of find steps)
// ctxt - the context (a framestack)
// t - the focus (a tree)
// l,u - lower and upper bound on keys appearing in the focus t
define find_step(k,ctxt,t,l,u) = {
  if (t is a leaf) then return (ctxt,t,l,u)
                                // NB t is a node... (t0,k0,...,k(n-1),t(n))
  i <- get_child_index (k0,...) k     // find i st k(i-1)<=k<k(i)
                                // t is a node ... k(i-1) ti ki ...
  frame <- t[ ]i                 // new frame, with hole at t(i)
  ctxt <- cons(frame,ctxt)      // add frame to context
  t <- t(i)                     // set focus to child t(i)
  l <- if i>0 then k(i-1) else l  // update l
  u <- if i<n then k(i) else u  // update u
  return (ctxt,t,l,u)           // return updated values
}
\end{verbatim}

The main find routine then repeatedly applies the step function until
a leaf is reached.

\begin{verbatim}
define find(k,t) = {
  ctxt <- empty               // initial values...
  l <- -inf
  u <- +inf
  while(t is not a leaf) {    // repeatedly apply find_step
    ctxt,t,l,u <- find_step(k,ctxt,t,l,u)
  }
  // t is a leaf
  return (value associated with k in leaf t, if any)
}
\end{verbatim}


It is better to work with the following version of find that returns
the leaf itself:


\begin{verbatim}
define find(k,t) = {
  ctxt <- empty               // initial values...
  l <- -inf
  u <- +inf
  while(t is not a leaf) {    // repeatedly apply find_step
    ctxt,t,l,u <- find_step(k,ctxt,t,l,u)
  }
  // t is a leaf
  return (k,ctxt,t,l,u)
}
\end{verbatim}

This version is used in the insert and delete operations.



## Correctness of find

Let $s$ be the original tree. We wish to show:

*Lemma:* When $find\ k\ s$
terminates, it returns $ctxt,t,l,u$ such that:

//  - $t$ is a subtree of $s$
//  - $ctxt[t]$ is the original tree 
//  - for any $k'$ st. $l \le k' < u$, we have $m_s(k') = m_t(k')$
//  - $l \le k < u$

- $t$ is a leaf
- $m_s(k) = m_t(k)$

In fact, at any point during the execution of find, if $t$ is the
focus, then the property $P(k,ctxt,t,l,u)
= (m_s(k) = m_t(k))$ is a T-invariant on (wellformed) states of find, where T is the
set of find-step transitions. 

*Proof:* Assume a find-step transition ${}(k,ctxt,t,l,u) \rightarrow
(k,ctxt',t',l',u')$. Assume $P(...t...)$ holds, i.e., $m_s(k) =
m_t(k)$. To show $m_s(k) = m_{t'}(k)$, it suffices to show $m_t(k) =
m_{t'}(k)$. By definition of find-step, $t' = t_i$, where $k \in
K_i$. By definition of $m_t$, $m_t$ is the disjoint union of
$m_{t_j}$, and by wellformedness of $t$, $m_t(k) = m_{t_i}(k)$.

*Note:* by "wellformed states of find" we mean states where the focus
(at least!) is a wellformed search tree. This property is itself
T-invariant (!) in the sense that find-step maps wellformed states to
wellformed states.

From the lemma, it follows that $m_s(k) = m_t(k)$, where $m_t$ is the
map formed from the leaf $t$ returned by find.

In fact, much more informative properties hold (for example, we have
not said anything here about $l$ and $u$), but this suffices for
the correctness of find.



# Insert

The insert operation is more complicated than find, because it
potentially involves splitting nodes that are too big.


## Simple example

The simple case arises when we insert a new $(k,v)$ pair into a leaf
and the resulting leaf is not too big (according to
max-leaf-keys). For example, consider the following tree:

\includegraphics{pics/insert10.dot.pdf}

Suppose we wish to insert a new key $5$ and associated value. We can
use find to locate the leaf $4,6$, and after inserting $5$ we get a
new leaf $4,5,6$, which we then place back into the context to
construct the new tree with the additional key:

\includegraphics{pics/insert11.dot.pdf}

Unfortunately not all cases are this simple.


## Example involving splitting the leaf

Consider the following tree:

\includegraphics{pics/insert12.dot.pdf}

Suppose max-leaf-keys is 3. Suppose we attempt to insert the key
$4$. We descend the tree, arrive at the leaf, insert the key, and
obtain the new leaf $1,2,3,4$. Unfortunately this is too big, so we
need to split it into two leaves $1,2$ and $3,4$ separated by the
key 3. Instead of a leaf, we now have a tree as the focus:

\includegraphics{pics/insert13.dot.pdf}

We then insert this *tree* into the context to get the final tree:

\includegraphics{pics/insert14.dot.pdf}


## Example involving splitting a node

If we split a leaf, we increase by one the number of keys in the
parent. This can cause the parent node to become too big, so that it
must be split in turn. For example, if max-node-keys was 4, we would
take the following focus:

\includegraphics{pics/insert20.dot.pdf}

and split it to get a new focus:

\includegraphics{pics/insert21.dot.pdf}

And similarly to the leaf case, we would then insert this into the context (assuming the
context is not empty).

## Pseudocode for insert

Pseudocode for insert is as follows.

TODO find to locate leaf; insert kv; split leaf; repeatedly step up

\begin{verbatim}
// inputs:
// ctxt - the ctxt from find'
// focus - a focus, either a tree [t1], or a pair of trees separated by a key [t1,k,t2]

define insert_step_up(ctxt,focus) = {
  case focus matches [t1] {
    t[_] <- hd(ctxt)
    ctxt <- tl(ctxt)
    focus <- t[t1]  // place t1 in t[_] and make new focus
    return (ctxt,focus)  
  }
    
  case focus matches [t1,k,t2] {
    t[_] <- hd(ctxt)
    ctxt <- tl(ctxt)
    focus <- t[t1,k,t2]  // TODO define this!
    (if (focus too big) then focus <- split(focus)); // TODO define
    return (ctxt,focus)    
  }
}
\end{verbatim}



## Split leaf focus, formally

We now treat the case where the leaf is split more formally.

The focus is a leaf $k_0,\ldots,k_n$ where $n$ is the maximum leaf
size. Since there are $n+1$ keys in the leaf, it must be split into
two smaller leaves $c_1$ and $c_2$: 

$c_1 = k_0,...,k_{i-1}$ and $c_2 = k_i,\ldots,k_{n}$

Here we choose $i = \lfloor n/2 \rfloor$ so there are $i$ keys in the
first child and $n+1-i$ in the second. 

*Note on size constraints:* Clearly we require 
$\textit{min-leaf-keys} \le \lfloor \textit{max-leaf-keys}/2 \rfloor$.

The focus is now a node: 

$_{c_1}|^{k_i}|_{c_2}$

*Note:* that the focus has changed from a leaf to a tree.

Now consider the context which (if non-empty) starts with a frame: ${}\ldots{}|^k|_{\Box}|^{k'}|\ldots$

If we insert the new focus into the frame we get a new focus:

${}\ldots{}|^k|_{c_1}|^{k_i}|_{c_2}|^{k'}|\ldots$.

Note that there is 1 more key in this node than the frame from which
it was created, and so this focus may in turn need to be split.


// # $\ldots|_{k_0, k_1, \ldots, k_{2n}}|^{k}|\ldots %
// # \rightarrow %
// # 

*Example:* Suppose the context is
$_{\Box}|^6|_{t_1}|^{10}|_{t_2}|^{14}|_{t_3}|^{18}|_{t_4}$. Focus is
the leaf $1,2,3,4$. Inserting new key 5 into the leaf gives an updated leaf
$1,2,3,4,5$. After splitting, we have a new focus
$_{1,2}|^3|_{3,4,5}$.

If we now insert this focus into the context, we get a new node focus
$_{1,2}|^3|_{3,4,5}|^6|_{t_1} | \ldots$

// # FIXME max leaf size can be 3, because splitting doesn't remove a kv.
// # 
// # Max node keys ... splitting a node


## Split node focus, formally

The focus is a node $t_0,k_0,\ldots, k_n,t_{n+1}$ where $n = \textit{max-node-keys}$ is the max
number of node keys. Since there are $n+1$ node keys, we must split
the node to get a new node with two children:

$_{\ldots,k_{i-1},t_i}|^{k_i}|_{t_{i+1},{k_{i+1}},\ldots}$

We can choose $i = \lfloor \textit{max-node-keys}/2 \rfloor$.

Before we had $n+1$ keys. Now we have $i$ keys in the first child and
$n-i$ in the second child, with the remaining key used to separate the children.

*Note on size constraints:* Clearly we require $\textit{min-node-keys}
\le \lfloor \textit{max-node-keys}/2 \rfloor$.


// # first child: k0...k_{m-1} gives m keys
// # second child: k(m+1)...k(m+m) gives m keys

Now consider what happens when we insert this new focus into the
context. For a context ${}\ldots|^k|_{\Box}|^{k'}\ldots$ we must insert
a tree of the form $_{c_1}|^{k_i}|_{c_2}$ between $k$ and $k'$,
resulting in a node
$\ldots|^k|_{c_1}|^{k_i}|_{c_2}|^{k'}\ldots$. Note that in this case,
the number of keys (in the parent of the original node) increases by
1, and this new focus may in turn need to be split.


*Example:* Suppose the focus is a node 

$_{t_0}|^3|_{t_1}|^6|_{t_2}|^{10}|_{t_3}|^{14}|_{t_4}|^{18}|_{t_5}$.

Suppose max-node-keys is $4$. In this case, we split the focus to get:

$_{c_1}|^{10}|_{c_2}$ where $c_1 = _{t_0}|^3|_{t_1}|^6|_{t_2}$ and
$c_2 = _{t_3}|^{14}|_{t_4}|^{18}|_{t_5}$.

This is the new focus which we then proceed to insert into the first
frame in the context (if any).



## TODO Phases, sequence of operations

FIXME have a flowchart?

In the first phase we use $find'$ to locate the relevant leaf:
 
$t,k \rightarrow ctxt,focus_1$

Then we insert the new ${}(k,v)$ pair into the leaf:

$focus_1 \rightarrow_{insert} focus'$

If the leaf is too big, we split the focus:

$focus' \rightarrow_{split} focus''$

Finally, we combine the focus with the first frame in the context to
get a new focus:

$frame,focus'' \rightarrow_{combine} focus_2$

*Note:* for the non-leaf case, we have a (node) focus, which we
combine with the frame to get a new focus, which we may need to
split. Then we continue with the next frame.

## TODO Beyond the simple example

Suppose the leaf is of the form ${}(k_0,v_0),(k_1,v_1),\ldots$. If the
leaf is not already at the maximum size allowed, we can just insert
the new key-value pair to obtain a new leaf, which we then combine
with the context to obtain a new tree. If the leaf already contains
$k$, we can update with the new key-value pair even if the leaf has
maximum size.

The difficult case to handle occurs when the leaf has maximum size
and adding the new pair would result in a leaf that is too big. In
this case, the leaf of length $max_{leaf}+1$ is divided into two
leaves, separated by a key. Suppose we divide at position $i$. Then
leaf 1 is $kv_0,kv1,\ldots,kv_{i-1}$ and leaf 2 is
${}(k_i,v_i),\ldots$, and clearly these leaves are separated by $k_i$,
in the sense that $leaf_1,k_i,leaf_2$ is a valid partition. FIXME 

Let's rename the components ${}(l_1,k_l,l_2)$.

Suppose the context has frame
${}(\ldots,t_{i-1},k_{i-1}),(k_i,t_{i+1},\ldots)$ at the head
(corresponding to the parent of the leaf). Clearly we could insert the
new leaves to get a new node
${}(\ldots,k_{i-1},l_1,k_l,l_2,k_i,\ldots)$. However, it may well be
the case that this node in turn is too big, since it has one more
child than the original. In this case, we must again split the node,
and continue with the next frame on the framestack. 

Eventually we may end up with a root that is too big, at which point
we split the root in two, and create a new root with two children. At
this point, the height of the tree grows by one.


---




# Note on choice of minimum and maximum sizes

A possible choice: min-leaf-keys=$l$; max-leaf-keys=$l'$; min-node-keys=$m$;
max-node-keys=$m'$

Write these bounds as: leaf:(l,l'), node:(m,m')

Examples: (leaf:(2,3), node:(2,4))  FIXME check that these are indeed valid

In this case, if we try to insert into a leaf with 3 keys, we split to
get 2 leaves with 2 keys each. For a node, if we have $4$ keys and we
insert another, we split to get two nodes, each with $2$ keys (the
remaining key is used to separate these two nodes).

Clearly for a leaf we require $l<= \lfloor {(l'+1)/2} \rfloor$.

For a node, if $m' = 2m''+1$ is odd, then we require $m <=
m''$. Otherwise $m <= m'/2$. In short, $m <= \lfloor (m'+1)/2 \rfloor$


# Delete

Delete is considerably more complicated than insert. Insert involves
splitting nodes. Delete involves merging nodes, and additionally
delete has many cases that involve "stealing" keys and children from
neighbouring nodes. These operations are similar to the "rotations"
encountered when balancing red-black trees (and other similar
datastructures). These additional cases are many because we must treat
nodes and leaves differently, and must also distinguish between
stealing and merging from the right or the left. Thus, it is important
that we try to treat these cases uniformly as far as possible, in
order to mitigate the explosion of cases.

TODO talk about root case

## Steal right (node)


FIXME update following latex to follow more closely the verbatim for
this case; NOTE ki ri are numbered sequentially and in increasing
order (so k1 lt k2 etc)

We now develop some syntax to treat the various cases.

Suppose $t=t_0,k_0,\ldots$ and we are focused on child
$t_i$. We typically deal with left and right siblings. Let's say that
we are interested in the right child.

// #+INCLUDE: "./steal_right_node.org"

steal right node:

\begin{verbatim}
Initial parent state:
| ... | k1 |     | k2 |   | k5 | ... |
|     |    | (c) |    | d |    |     |

c points to
| ... | X |   | ==> | ... | X |   | k2 |    |
|     |   | X |     |     |   | X |    | r1 |

d points to 
|    | k3 |    | k4 | ... | ==> |    | k4 | ... |
| r1 |    | r2 |    |     |     | r2 |    |     |


Final parent state:

| ... | k1 |      | k3 |    | k5 | ... |
|     |    | (c') |    | d' |    |     |
\end{verbatim}


Using reduced mathematical notation (don't expect the variables to
match up FIXME):

% https://tex.stackexchange.com/questions/334008/how-to-create-a-box-with-a-superscript
\newcommand{\boxsym}[1]{%
[#1]}


$$
\ldots|_{\boxsym{\ldots_1,k_?,r_?}}|^{k_1}|_{(r_2,k_2,\ldots_2)}|\ldots %
\rightarrow %
\ldots|_{r_3(\ldots_1,k_?,r_?,k_1,r_2)}|^{k_2}|_{r_4(\ldots_2)}|\ldots
$$



NOTE: the focus is not on disk, so is not pointed to by a reference

NOTE: by the time we decide to steal right, we have already read the
right sibling from disk.

*Note on how to interpret this diagram:* In the above diagram, we show
only what changes. We are dealing with 3 nodes: the parent, the left
child and the right child. Although we are dealing with block
references, we omit this and instead represent the trees directly. The
focus is the node ${}[\ldots,k_?,t_?]$. The key $k_1$ is a key in the
parent (in fact, it is the first key in the right hand side of the
split parent FIXME explain split). After transformation, we again have
3 nodes, but the left child has gained $k_1,t$ and the parent key
which separates the left child from the right child has changed to
$k_2$. FIXME reconcile this with above


*Sequence of events:* $r_1$ is followed to read $r_2,\ldots$. New node
is constructed and written to give $r_3$. Similarly for
$r_4$. Finally, separating key is changed to $k_2$, and the new parent
node thus formed becomes the new focus.


Note that it seems very useful to have a function `dest_right_node`
which produces $rt,rk,r$, and similarly for left node.

TODO have concrete examples to demonstrate these cases


## Steal left (node)

steal left node:

$$\ldots|_{\ldots_1,k_1,r_1}|^{k_2}|_{[\ldots_2]}|\ldots %
\rightarrow %
\ldots|_{r_3(\ldots_1)}|^{k_1}|_{r_4(r_1,k_2,\ldots_2)}|\ldots
$$







## Steal right (leaf)

$$
\ldots|_{r_?(\ldots_1,k_1)}|^{k_2}|_{r_?(k_3,k_4,\ldots_2)}|\ldots %
\rightarrow %
\ldots|_{r_1(\ldots_1,k_1,k_3)}|^{k_4}|_{r_2(k_4,\ldots_2)}|\ldots
$$

Note that this takes only one kv, whereas the node case moves a
subtree and a key.






## Steal left (leaf)

$$
\ldots|_{r_?(\ldots_1, k_1, k_2)}|^{k_3}|_{[r_?(k_4, \ldots_2)]}|\ldots %
\rightarrow %
\ldots|_{r_1(\ldots_1, k_1)}|^{k_2}|_{[r_2(k_2, k_4, \ldots])}|\ldots
$$

// #+INCLUDE: "./steal_left_leaf.org"

Note carefully the difference between this case and steal right
(leaf): the role of the keys lk and rk are different, sine here lk is
promoted to the parent, whereas in the right case, it is the key rk'
that is promoted. This arises because of the asymmetry on the order of
the keys and the children they flank: $k \le t_i < k'$.


~dest_left_leaf~ gives $l,lk$



## Merge {right,left} (node)


$$
\ldots|_{r_?(\ldots_1, k_1, r_1)}|^{k_2}|_{r_?(r_3, k_3, \ldots_2)}|\ldots %
\rightarrow %
\ldots|_{r_4(\ldots_1, k_1, r_1, k_2, r_3, k_3, \ldots_2)}|\ldots
$$

Note that this picture also works for merge left (node), but must be
careful about the split node and reversing.

Note that this causes the parent to have one less key, possibly
becoming too small. For the root, with only one key, the result may be
a root with no keys, in which case the height of the tree decreases
by 1.


## Merge {right,left} (leaf, easy)

$$
\ldots|_{r_?(\ldots_1, k_1)}|^{k_2}|_{r_?(k_3, \ldots_2)}|\ldots %
\rightarrow %
\ldots|_{r_1(\ldots_1, k_1, k_3, \ldots_2)}|\ldots
$$

Note that, as above, this causes the parent to have one less key, and
the parent could be the root with only one key.

TODO explain how these pictures work!

FIXME put these in a table

FIXME perhaps rewrite delete code along these lines? probably best to
spell out all the cases explicitly, with an aux function indicating
whether to steal or merge, and whether this is left or right.


TODO: for code, we may want to isolate the parts that can potentially change

| k1 |   | k2 |   | k3 |   | k4 |
|    | l |    | c |    | r |    |

or perhaps we just deal with the cases one by one, explicitly?

These mutations would be easy to check in Isabelle

## Commentary on store interactions leading up to and including leaf-merge-right

- We first examine the parent ts2 to see if there is a right
sibling. 
- Assuming there is, we then read the right sibling from
store. 
- We then form a merged leaf, write this, obtain the resulting
ref...
- update the parent frame with the new ref and new keys, and then
  continue with this as the new focus (without writing it... yet!)





# following in btree_doc.org
# Leaf stream
# Insert many
# Reading from a given range

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
