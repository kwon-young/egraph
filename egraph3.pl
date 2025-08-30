:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs for Prolog terms using logic variables as mutable unique identifiers.
Each class is keyed by a fresh Id variable whose only mutation is aliasing via
(=)/2 and whose equality must be tested with (==).

Key ideas.
Nodes are an ordset of Key-Id pairs where Key is an atom, a var, or F(ChildIds).
Keys preserve variable identity and are never alpha-renamed or normalized.
Ids are opaque logic variables and must never be inspected or printed as names.
Canonicalization keeps at most one Key-Id per Key and is performed by
merge_nodes/2 after any aliasing.

Execution model (DCG pipeline).
Rules are pure producers that emit Key-Id pairs and equalities A=B and they must
not inspect or bind Ids.
Only rebuild//1 and merge_nodes/2 perform Id aliasing and they must be run
after rules to propagate effects and re-canonicalize.

Public API.
add//2 inserts a term as nodes and returns its class Id via DCG.
union//2 aliases two class Ids via DCG and re-canonicalizes.
saturate//1 runs the fixed-point driver with an unbounded step budget.
saturate//2 runs the driver with a bounded step budget.
extract//0 aliases each class Id to a representative Key via DCG.
extract/1 aliases each class Id to a representative Key in place.

Driver.
saturate iterates make_index, match, rebuild, and merge until the node count
stabilizes and alias-only steps do not count as progress.

Determinism and discipline.
Ids are compared by identity with (==) and never by name or print-name.
Unifying Ids may instantiate variables inside Keys and a subsequent merge collapses
any resulting collisions.
lookup/2 expects canonicalized input and non-canonical sets may fail spuriously.

Known limitations.
Keys are intentionally variable-identity sensitive so variant-equal Keys with
distinct variables are different.
assoc//2 contains a cut and fails when BC is absent from the Index while the
intended behavior is to emit no output.

Goal of extract.
The goal of extract is to unify each class Id with a representative Key in order
to obtain a concrete Prolog term per class and it is the last standard step of
using an e-graph and should not be followed by rewriting or saturation.

Predicate index (concise).
lookup/2 finds the Id for a Key in a canonical ordset in O(N) time.
add//2 and add/4 build nodes for a term and emit Key-Id without aliasing.
add_node/3 and add_node/4 insert or reuse a Node-Id in a canonical ordset.
union//2 and union/4 alias two Ids and then re-canonicalize.
merge_nodes//0 and merge_nodes/2 deduplicate by Key and unify duplicate Ids.
merge_group/4 unifies the tail Ids with the head and reports if changes occurred.
comm//2 emits the commuted +(B,A) node and AB=BA for +(A,B).
assoc//2 emits AB, (AB+C), and ABC=ABC_ for (A+(B+C)) filtered by class(BC).
assoc_//3 iterates the class of BC and emits at most one triple per +(B,C).
reduce//2 emits A=AB when class(B) contains the integer 0.
constant_folding//2 emits VC-C and C=AB for numeric VA in class(A) and VB in
class(B) with VC is VA+VB.
constant_folding_a//4 picks numeric VA from class(A) and delegates to _b.
constant_folding_b//4 pairs numeric VB in class(B) with VA and emits folds.
rules//3 applies a list of rules to a node in order using an Index.
rule//3 is a thin wrapper that invokes one rule for a node and Index.
make_index/2 builds an rbtree mapping Id to the Keys in its class.
match/4 runs rules over a worklist and produces scheduled matches.
push_back//1 appends a list to DCG output as a scheduling helper.
rebuild//1 consumes equalities by aliasing Ids, enqueues pairs, and merges.
saturate//1 and saturate//2 are DCG drivers and saturate/4 is the pure driver.
unif/1 recognizes A=B and performs Id aliasing and is used by rebuild only.
extract/1, extract//0, and extract/2 alias Ids to representatives for materialization.
extract_node/1 chooses a representative per class and backtracks over choices.
add_expr/2 builds a left-associated addition chain 1+2+...+N for N>=1.
example1/1 builds a small graph, performs a union, and returns the nodes.
example2/2 builds and saturates an addition chain and prints a size sanity check.
example3/3 enumerates extracted results after saturation and removes duplicates.

Notes.
The use of logic variables as mutable class identifiers is subtle and requires
strict separation of concerns where only rebuild and merge_nodes unify Ids.
*/

/* ----------------------------------------------------------------------
   Predicate overview (one sentence per line; <= 80 columns).
---------------------------------------------------------------------- */

%% lookup/2
% lookup/2 finds the Id for a Key in a canonical ordset and compares Keys with
% (==).

%% add//2
% add//2 adds a term as nodes via DCG and yields its class Id without aliasing
% Ids.

%% add/4
% add/4 adds a term to a node set and returns the updated set without aliasing
% Ids.

%% add_node/3
% add_node/3 inserts Node-Id into a canonical set or reuses the existing Id in
% place.

%% add_node/4
% add_node/4 inserts Node-Id given as a pair or reuses the provided Id if
% present.

%% union//2
% union//2 aliases two class Ids via DCG and then re-canonicalizes the node
% set.

%% union/4
% union/4 aliases two class Ids in place and then merges duplicate Keys
% deterministically.

%% merge_nodes//0
% merge_nodes//0 wraps merge_nodes/2 in DCG and performs no aliasing itself.

%% merge_nodes/2
% merge_nodes/2 deduplicates by Key, unifies duplicate Ids, and repeats until
% stable.

%% merge_group/4
% merge_group/4 unifies all Ids in a duplicate group with the head and flags
% changes.

%% comm//2
% comm//2 emits the commuted node B+A and AB=BA for a +(A,B) node.

%% assoc//2
% assoc//2 emits (A+B), (AB+C), and ABC=ABC_ for (A+(B+C)) using class(BC) from
% Index.

%% assoc_//3
% assoc_//3 iterates class(BC) and emits at most one triple per +(B,C) member.

%% reduce//2
% reduce//2 emits A=AB when class(B) contains the integer 0 and otherwise emits
% nothing.

%% constant_folding//2
% constant_folding//2 folds numeric sums by emitting VC-C and C=AB when VA and
% VB are numbers.

%% constant_folding_a//4
% constant_folding_a//4 selects numeric VA from class(A) and delegates to
% constant_folding_b//4.

%% constant_folding_b//4
% constant_folding_b//4 pairs numeric VB with VA, computes VC is VA+VB, and
% emits folds.

%% rules//3
% rules//3 applies a list of rules to one node and concatenates their outputs in
% order.

%% rule//3
% rule//3 invokes one rule for a node and index and forwards its output
% unchanged.

%% make_index/2
% make_index/2 builds an rbtree Id->[Keys] from canonical nodes and must be
% rebuilt after aliasing.

%% match/4
% match/4 runs rules over a worklist and returns scheduled matches in a stable
% order.

%% push_back//1
% push_back//1 appends a list to DCG output using difference lists in O(1).

%% rebuild//1
% rebuild//1 consumes equalities by aliasing Ids, enqueues pairs, and
% re-canonicalizes.

%% saturate//1
% saturate//1 runs the driver to a length fixpoint while ignoring alias-only
% steps.

%% saturate//2
% saturate//2 runs the driver with a step bound and stops early on a fixpoint.

%% saturate/4
% saturate/4 is the pure driver used by saturate//2 and saturate//1.

%% unif/1
% unif/1 recognizes A=B and performs Id aliasing and is only called by
% rebuild//1.

%% extract/1
% extract/1 aliases each class Id to a representative Key and produces concrete
% terms.

%% extract//0
% extract//0 is the DCG wrapper around extract/1 and is the last standard step
% to run.

%% extract/2
% extract/2 is the semidet in-place form that aliases and returns the node list
% unchanged.

%% extract_node/1
% extract_node/1 chooses a representative Key per class and backtracks over
% choices.

%% add_expr/2
% add_expr/2 builds the left-associated addition chain 1+2+...+N for N>=1.

%% example1/1
% example1/1 builds a small graph, performs a union, and returns the final
% nodes.

%% example2/2
% example2/2 builds and saturates an addition chain and prints size sanity
% checks.

%% example3/3
% example3/3 enumerates extracted results after saturation and removes
% duplicates.

/* Notes.
   Ids are logic variables used as mutable unique identifiers and must be
   compared with (==).
   Keys preserve variable identity and are never alpha-renamed or normalized.
   Only rebuild//1 and merge_nodes/2 unify Ids and rules must never inspect or
   bind them.
   The goal of extract is to obtain a concrete Prolog term per class and it
   should be the last step. */


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%% Implementation reference (concise; one sentence per line).
%% Ids are logic variables used as mutable class identifiers and only (=)/2 may alias them.
%% Keys preserve variable identity and must be compared with (==).
%% lookup/2 finds the Id for a Key in a canonical ordset in O(N) time.
%% add//2 and add/4 insert a term as nodes and emit Key-Id without aliasing.
%% add_node/3 and add_node/4 insert or reuse a Node-Id and keep the set canonical.
%% union//2 and union/4 alias two Ids and then re-canonicalize with merge_nodes/2.
%% merge_nodes//0 and merge_nodes/2 deduplicate by Key and unify duplicate Ids.
%% merge_group/4 unifies the tail Ids with the head and reports if changes occurred.
%% comm//2 emits the commuted +(B,A) and AB=BA for +(A,B).
%% assoc//2 emits AB, AB+C, and ABC=ABC_ for A+(B+C) filtered by class(BC).
%% NOTE: assoc//2 currently fails when BC is absent due to a cut and should emit no output.
%% assoc_//3 iterates class(BC) members and emits at most one triple per +(B,C).
%% reduce//2 emits A=AB when class(B) contains the integer 0 and otherwise emits nothing.
%% constant_folding//2 emits VC-C and C=AB for numeric VA in class(A) and VB in class(B).
%% constant_folding_a//4 picks numeric VA from class(A) and delegates to constant_folding_b//4.
%% constant_folding_b//4 pairs numeric VB in class(B) with VA and emits folds.
%% rules//3 applies a list of rules to a node in order using an index.
%% rule//3 invokes one rule for a node and index and forwards its output unchanged.
%% make_index/2 builds an rbtree mapping Id to the Keys in its class.
%% match/4 runs rules over a worklist and produces scheduled matches.
%% push_back//1 appends a list to DCG output as a scheduling helper.
%% rebuild//1 consumes equalities by aliasing Ids, enqueues pairs, and merges.
%% saturate//1 runs the driver to a length fixpoint and ignores alias-only steps.
%% saturate//2 runs the driver with a step bound and stops early on a fixpoint.
%% saturate/4 is the pure driver used by the DCG forms.
%% unif/1 recognizes A=B and performs Id aliasing and is used only by rebuild//1.
%% extract/1 aliases each class Id to a representative Key to produce concrete terms.
%% extract//0 is the DCG wrapper around extract/1 and is the last standard step to run.
%% extract/2 aliases and returns the node list unchanged in a semidet in-place form.
%% extract_node/1 chooses a representative Key per class and backtracks over choices.
%% add_expr/2 builds the left-associated addition chain 1+2+...+N for N>=1.
%% example1/1 builds a small graph, performs a union, and returns the nodes.
%% example2/2 builds and saturates an addition chain and prints size sanity checks.
%% example3/3 enumerates extracted results after saturation and removes duplicates.
%% Notes.
%% The goal of extract is to extract a concrete prolog term per class and it is the last standard step.
%% Only rebuild//1 and merge_nodes/2 may unify Ids and rules must not inspect or bind them.

%! lookup(+Key-?Id, +Pairs) is semidet.
%  Find Id for Key in a canonical ordset of Key-Id pairs.
%  - Pre: Pairs canonical (run merge_nodes/2 after aliasing).
%  - Method: prune by standard order; confirm Key identity with (==); only binds Id.
%  - Det/Big-O: semidet, steadfast; O(N); no choicepoints on success.
%  Notes:
%  - Non-canonical input may fail by design (precondition is canonical).
%  - Ids are logic variables; compare with (==) only.
%  - Keys keep variable identity; do not alpha-normalize or use =@=/2.
%  - Variant-equal but non-identical keys do not match (intended; see egraph3.plt).
lookup(Item-V, [X1-V1, X2-V2, X3-V3, X4-V4|Xs]) :-
   !,
   compare(R4, Item, X4),
   (   R4=(>)
   ->  lookup(Item-V, Xs)
   ;   R4=(<)
   ->  compare(R2, Item, X2),
      (   R2=(>)
      ->  Item==X3, V = V3
      ;   R2=(<)
      ->  Item==X1, V = V1
      ;   V = V2
      )
   ;   V = V4
   ).
lookup(Item-V, [X1-V1, X2-V2|Xs]) :-
   !,
   compare(R2, Item, X2),
   (   R2=(>)
   ->  lookup(Item-V, Xs)
   ;   R2=(<)
   ->  Item==X1, V = V1
   ;   V = V2
   ).
lookup(Item-V, [X1-V1]) :-
   Item==X1, V = V1.

%! add(+Term, -Id)// is det.
%! add(+Term, -Id, +In, -Out) is det.
%  Ensure a node for Term exists; return its class Id (fresh or reused).
%  - Compound: Key = F(ChildIds) built left-to-right (stable congruence).
%  - Atom/var:  Key = Term (variable identity is part of the Key).
%  - Emits Key-Id only; never aliases Ids (dedup via merge_nodes/2).
%  Pre: In is an ordset (canonical preferred).
%  Det/Complexity: det; steadfast.
%  Build O(|Term|) and insert O(N) via ord_add_element/3.
%  Notes:
%  - Allocates at most one fresh Id (logic variable) if absent.
%  - DCG form is a pure producer (no Id aliasing).
add(Term, Id, In, Out) :-
   (  compound(Term)
   -> Term =.. [F | Args],
      foldl(add, Args, Ids, In, Tmp),
      Node =.. [F | Ids],
      add_node(Node, Id, Tmp, Out)
   ;  add_node(Term, Id, In, Out)
   ).

%! add_node(+Node-?Id, +In, -Out) is det.
%! add_node(+Node, -Id, +In, -Out) is det.
%  Insert Node-Id into canonical ordset In if absent; Out is canonical.
%  - If present: reuse Id, Out=In; else: insert with a fresh Id variable.
%  - Uses standard order and (==) on Keys; no re-sorting needed.
%  - Never unifies Ids; ord_add_element/3 enforces set semantics.
%  Pre: In canonical.
%  Det/Complexity: det; O(N). Quasi-pure (may allocate one fresh Id).
%  Notes:
%  - Ids are logic variables (mutable class IDs); compare by identity (==), never by name.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%! union(+IdA, +IdB, +In, -Out) is det.
%  Alias classes by unifying IdA with IdB; then merge_nodes/2 to re-canonicalize.
%  - Only Id variables unify; Keys never do. Unifying Ids can instantiate variables inside Keys; the next merge collapses collisions.
%  - Uses (=)/2 (no occurs-check); safe for fresh, acyclic Ids; backtrackable.
%  Det/Effects: det; effect is Id aliasing only (backtrackable).
%  Notes:
%  - Ids are logic variables acting as mutable unique IDs; compare by identity (==), never by name.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG wrapper for merge_nodes/2; emits nothing. Pure producer.
%  Note: On SWI-Prolog, DCG expansion calls merge_nodes/2 directly.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize Nodes to at most one Key-Id per Key; repeat while any group merges.
%  - Steps: sort -> group -> unify all Ids in each group with the first (representative).
%  - Only Id variables unify; Keys never do. Aliasing may instantiate variables inside Keys; the next pass collapses collisions.
%  Complexity: O(N log N) per pass; repeats while merges occur.
%  Notes:
%  - Out canonical (sorted; one Key-Id per Key).
%  - Terminates: each merge strictly decreases the number of distinct Id variables.
%  - Representative Id is the first after sorting; do not rely on it across backtracking.
%  - Rebuild any Id→[Keys] index after this (Ids are the map keys).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  For Key-[H|T], unify all Ids in T with H; Changed=true iff T \= [].
%  - Only Id variables unify; Keys unchanged. Representative Id is H.
%  Complexity: O(|T|). det.
%  Notes:
%  - Id unification may instantiate variables inside Keys (collapsed next pass).
%  - Keys never unify; only Ids may alias.
%  - Changed carries the progress flag for merge_nodes/2.
%  - Uses (=)/2 via maplist(=(H), T); no occurs-check; safe for fresh Ids.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity of +/2: from (A+B)-AB emit B+A-BA and AB=BA.
%  - Models equality without in-place rewrite; at most one commuted variant per match.
%  Notes:
%  - BA is fresh; equality is consumed by rebuild//1 (Id aliasing only).
%  - Rules must not inspect or bind Ids; only emit nodes and (=)/2 between Ids.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restrict to members of class(BC) via Index; may emit multiple triples (one per matching B+C member).
%  Index: rbtree Id -> [Keys]; rebuilt each iteration; read-only.
%  - Limitation: if BC is absent from Index, a cut (!) causes this rule to fail instead of emitting no output ([]). Intended behavior is 'no output'.
%  Notes:
%  - AB and ABC_ are fresh; unification is deferred to rebuild//1 (Ids only).
%  - The Id for BC confines the search; never unify Keys here.
%  - Rules must not inspect or bind Ids; only emit nodes and (=)/2 between Ids.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC) with A fixed.
%  - Emit at most one triple per qualifying member; confine rewrites to the class.
%  Notes:
%  - Pure producer; must not inspect or bind Ids.
%  - Members are Keys from Index; unification happens later in rebuild//1 (Ids only).
%  Determinism: nondet over Members; tail-recursive; no side effects.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of +/2: if class(B) contains integer 0, emit A=AB.
%  - Uses once/1 to avoid duplicates; match the integer 0 exactly with (==).
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Unification happens in rebuild//1 (Ids only); rules must not inspect or bind Ids.
%  - Use strict term equality (==) to match integer 0 and not 0.0.
%  Determinism: semidet; pure producer.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums for +/2 into a constant.
%  - Introduce C where VC is VA+VB; emit VC-C and C=AB.
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Uses is/2; respects Prolog numeric semantics and mixed numeric types; pure
%    producer.
%  - Unification deferred to rebuild//1 (Ids only). Non-numeric members are skipped.
%  Determinism: nondet; no side effects; must not inspect or bind Ids.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Pick numeric VA in class(A), then search class(B) for numeric VB.
%  - Staged search avoids building pairs eagerly; guarded with number/1.
%  Notes:
%  - Pure producer; unification deferred to rebuild//1 (Ids only).
%  - Guards ensure only ground numeric values reach is/2 in the next stage.
%  Determinism: nondet over numeric members of class(A) and class(B); no side effects.
constant_folding_a([VA | ANodes], B, AB, Index) -->
   (  {number(VA)}
   -> {rb_lookup(B, BNodes, Index)},
      constant_folding_b(BNodes, VA, AB, Index)
   ;  []
   ),
   constant_folding_a(ANodes, B, AB, Index).
constant_folding_a([], _, _, _) --> [].
%! constant_folding_b(+ClassB, +VA, -AB, +Index)// is nondet.
%  For each numeric VB in class(B), compute VC is VA+VB and emit VC-C, C=AB.
%  Notes:
%  - number/1 guards ensured by constant_folding_a//4.
%  - Supports mixed numeric types; result type follows is/2 semantics.
%  - Pure producer; unification deferred to rebuild//1 (Ids only); must not
%    inspect or bind Ids.
%  Determinism: nondet over numeric members of class(B); no side effects.
%  The emitted VC-C is a new Key-Id pair; equality C=AB is consumed by
%  rebuild//1.
constant_folding_b([VB | BNodes], VA, AB, Index) -->
   (  {number(VB)}
   -> {VC is VA + VB},
      [VC-C, C=AB]
   ;  []
   ),
   constant_folding_b(BNodes, VA, AB, Index).
constant_folding_b([], _, _, _) --> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply Rules to Node using Index; append outputs in rule order. Each Rule is a DCG nonterminal Rule(Node,Index)//2.
%  - Node is Key-Id; rules may emit only Key-Id items and (=)/2 between Ids.
%  - Uses sequence//2 from library(dcg/high_order). Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Pure producer; steadfast; Ids are opaque mutable identifiers (do not inspect/bind).
%  - Output order: per-node, then per-rule. Do not rely on representative Ids.
%  - Rules are independent; side effects happen only in rebuild//1 (Id aliasing).
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Invoke Rule(Node,Index)//2 on Node.
%  Notes:
%  - Pure producer; steadfast; Ids are opaque (do not inspect/bind).
%  - Determinism follows Rule//2. Kept separate for clarity with sequence//2.
%  - Thin wrapper to adapt sequence//2 calling convention.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build rbtree Index mapping Id -> [Keys] from canonical Nodes.
%  - Pre: Nodes canonical (merge_nodes/2).
%  - Rebuild after any Id aliasing (Ids are the map keys).
%  - Ids are logic variables (mutable class IDs); keyed by variable identity (==), not by name/print-name.
%  Complexity/Determinism: O(N log N); det; pure; steadfast.
%  Impl: transpose_pairs/2 flips Key-Id to Id-Key; Keys are stored as-is (no unification).
%  Notes:
%  - Uses transpose_pairs/2 and group_pairs_by_key/2 (autoloaded from library(pairs)).
%  - Result is rbtree(Id->[Keys]) with nonempty value lists; rebuild after any Id aliasing.
%  - Intended for the current iteration only; discard and rebuild after each rebuild//1 or merge.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist using Index; produce scheduled Matches (Key-Id items and (=)/2).
%  - Output order: worklist, then per-node rule order.
%  Impl: foldl/4 with rules//3.
%  Complexity: O(|Worklist|*|Rules| + |Matches|) plus per-Rule Index work.
%  Determinism: det; pure; steadfast (no Id unification here).
%  Notes:
%  - Rebuild Index after rebuild//1 (Ids may alias).
%  - Worklist is typically the current canonical Nodes.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to DCG output in O(1) via difference lists.
%  - Scheduling helper only; merge_nodes/2 handles canonicalization.
%  Notes:
%  - Implemented with the DCG idiom: push_back(L), L --> [].
%  - Pure w.r.t. Keys/Ids; no aliasing or inspection of Ids.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (Key-Id items and (=)/2 between Ids), then canonicalize:
%    - exclude(unif, Matches, NewNodes): perform Id aliasing (A=B); drop equalities.
%    - push_back(NewNodes): enqueue Key-Id items.
%    - merge_nodes: dedupe; propagate effects of Id aliasing.
%  Effects: only Id variables unify; variables inside Keys may instantiate and are collapsed by the next merge.
%  Det: det. Equalities must be between Ids (A and B are Id vars).
%  Notes:
%  - Rebuild any Id->[Keys] index after this (Ids are the map keys).
%  - Keys must never appear on the left/right of (=)/2.
%  - DCG call to merge_nodes//0 expands to merge_nodes/2.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Iterate Rules to a length fixpoint (after rebuild/merge).
%  - Pure producer; emits only Key-Id and (=)/2.
%  - Alias-only steps (only A=B) do not count as progress.
%  Portability: uses MaxSteps=inf for convenience.
%  On systems where inf in arithmetic raises an error, use saturate//2 with a
%  large integer bound.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run up to MaxSteps iterations; stop early when length stabilizes (after rebuild/merge).
%  - MaxSteps: integer >= 0 (prefer a large integer over 'inf' on systems without arithmetic over inf).
%  - Alias-only steps are ignored (no new Key-Id pairs).
%  Det: det.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Driver. Each iteration: make_index/2, match/4, rebuild//1 (aliases Ids), merge_nodes/2.
%  - Only rebuild//1 and merge_nodes/2 unify Ids.
%  - Ids are logic variables; rebuild Index after aliasing; never compare by name/print-name.
%  - MaxSteps: integer >= 0; use saturate//2 to select the bound portably.
%  Det: det.
%  Notes:
%  Progress is measured by list length after merge.
%  Alias-only steps are ignored.
%  - Worklist is the current canonical Nodes.
saturate(Rules, N, In, Out) :-
   (  N > 0
   -> make_index(In, Index),
      match(Rules, In, Index, Matches),
      rebuild(Matches, In, Tmp),
      length(In, Len1),
      length(Tmp, Len2),
      (  Len1 \== Len2
      -> (  N == inf
         -> N1 = N
         ;  N1 is N - 1
         ),
         saturate(Rules, N1, Tmp, Out)
      ;  Out = Tmp
      )
   ;  Out = In
   ).

%! unif(+Eq) is semidet.
%  Recognize Eq=(A=B) and perform A=B (Id aliasing). Only called by rebuild//1; never call from rules or user code.
%  - Uses (=)/2 (no occurs-check); safe for fresh, acyclic Id variables; effect is backtrackable.
%  - Only class Id variables may appear on either side; Keys must not.
%  Det: semidet; intentionally impure. Note: this is the only explicit Id unification outside merge_nodes/2.
unif(A=B) :- A=B.

%! extract(-Nodes) is semidet.
%  Extract a concrete Prolog term per class by unifying each class Id with a representative Key.
%  - This is the last standard step; do not run rewriting/saturation after extraction.
%  Effects: aliases Id variables (backtrackable). To inspect without aliasing, read Nodes directly.
%  Fails only if a class has no Keys (should not happen after merge_nodes/2).
%  Notes:
%  - Only Id variables unify; Keys never unify with each other.
%  - Ids are logic variables; compare by identity (==), never by name/print-name.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  DCG wrapper for extract/1. Final step: alias Ids to materialize one concrete Prolog term per class.
%  Nondet over representative choice; succeeds iff every class has at least one Key.
%  Prefer extract/1 outside DCGs.
%! extract(+Nodes, -Nodes) is semidet.
%  Alias each class Id with one of its Keys (a representative) and return Nodes unchanged.
%  Goal: obtain a concrete Prolog term per class; this is the last standard step; stop rewriting/saturation afterward.
%  Det: semidet; fails only if some class has no Keys; nondet over representative choice.
%  Notes:
%  - Only Id variables unify; Keys never unify with each other.
%  - Ids are logic variables; compare by identity (==), never by print-name.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  For each Id->[Keys], unify Id with one member; backtracks over choices; fails on empty groups.
%  Core of extraction; aliases Ids. Use only as the last step.
%  Det: semidet; nondet over representative choice.
%  Notes:
%  - Picks a representative via member/2; Keys do not unify with each other.
%  - Ids are logic variables; compare by identity (==), never by print-name.
extract_node([Node-Nodes | Groups]) :-
   member(Node, Nodes),
   extract_node(Groups).
extract_node([]).

%! example1(-G) is det.
%  Demo: add a, f(f(a)), union them, then add f^4(a); returns the graph G.
example1(G) :-
   phrase((
      add(a, A),
      add(f(f(a)), FFA),
      union(A, FFA),
      add(f(f(f(f(a)))), _FFFFA)
   ), [], G).


%! add_expr(+N, -Expr) is det.
%  Build left-associated sum 1+2+...+N as a +(A,B) chain: ((1+2)+3)+... . N >= 1.
add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

%! example2(+N, -Expr) is det.
%  Build an addition chain and saturate with comm/assoc; prints counts to current output.
%  Sanity-check size growth vs. the closed form.
%  Note: if calling outside a DCG, use phrase/3 to run saturate//2.
example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add(Expr, _), [], G),
   time(saturate([comm, assoc], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

%! example3(+N, +Expr, -R) is nondet.
%  Enumerate possible results R after saturating with all rules, then validate via extract//0.
%  Uses distinct/1 (SWI-Prolog) to remove duplicates.
%  Determinism: nondet over alternative extractions R.
example3(N, Expr, R) :-
   distinct(R, phrase((
      add(Expr, R),
      saturate([comm, assoc, reduce, constant_folding], N),
      extract
   ), [], _)).
