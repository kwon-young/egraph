:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs with congruence closure for Prolog terms.

Core model
- Nodes: ordset of Key-Id pairs (standard order). A Key is an atom/var or a term F(ChildIds). Variable identity is part of the Key (no alpha/variant normalization).
- Class Ids: fresh logic variables are the mutable, backtrackable class identifiers. Mutation is only by aliasing classes via (=)/2 on Id variables.
- Canonicalization: merge_nodes/2 collapses duplicates to a single Key-Id per Key; after each pass, an Id→Keys index is rebuilt.

Execution
- DCGs thread the node set as a difference list. Rules only emit Key-Id items and equalities A=B; they never perform unification themselves.
- rebuild//1 consumes equalities (unifies Ids), enqueues new items, then calls merge_nodes/2.
- Unifying Ids can instantiate variables inside Keys; merge_nodes/2 repeats until no further merges appear.

Caveats
- The fixpoint in saturate//2 is length-based; alias-only steps (A=B with no new pairs) do not change the length and are invisible to the stop test.
- Never serialize or compare Ids by print-name; treat them as opaque logic variables.
- extract//0 and extract/1 use member/2 and may alias Ids; both are for validation only. To inspect the graph without aliasing Ids, use the Nodes list directly.

Public API
- add//2, union//2, saturate//1, saturate//2, extract/1, extract//0.

Implementation predicates (internal)
- lookup/2 (semidet, pure, steadfast): Canonical ordset lookup of Id for Key. Prunes by standard order, confirms identity with (==) to preserve variable identity. Binds only Id; fails if absent. No allocation. Pre: canonical ordset (output of merge_nodes/2). O(N) worst case.
- add//2, add/4 (det, pure w.r.t. Keys): Build Key=F(ChildIds) left-to-right (stable arg order ⇒ congruence). Emit Key-Id items only; never unify Ids. Duplicates removed later by merge_nodes/2. Uses foldl/5; steadfast.
- add_node/4, add_node/3 (det, quasi-pure): Ensure Node has a class Id. Reuse if present; otherwise insert Node-Id with a fresh unbound Id. In/Out are ordsets. No canonicalization or Id unification. Out=In if Node already exists.
- merge_nodes//0, merge_nodes/2 (det, logical effects): Canonicalize to one Key-Id per Key via sort → group → unify-first; repeat until stable under Id aliasing. Only Id vars unify; Keys never do. Terminates because the number of distinct Id vars strictly decreases. Out is canonical.
- merge_group/4 (det, logical effects): For Key-[H|T], unify all Ids in T with H; Changed=true iff T is nonempty. Only Id vars unify; Keys never do.
- make_index/2 (det, pure): Build rbtree Id->[Keys] from canonical Nodes using the Id variable as the map key. Rebuild after any Id aliasing. O(N log N).
- rules//3, rule//3 (nondet, pure): Apply each DCG rule Rule(Node,Index)// to Node using Index. Rules may emit only Key-Id pairs and (=)/2; must not inspect or bind Ids. Output order: node order, then rule order.
- match/4 (det, pure): Run Rules over the worklist using Index; collect concrete outputs (nodes and (=)/2). No unification here; steadfast accumulator. Output order: worklist order, then per-node rule order.
- push_back//1 (det, pure): Append a list to DCG output in O(1) via difference lists; scheduling only.
- rebuild//1 (det, logical effects): Apply (=)/2 equalities (alias Ids), enqueue resulting Key-Id items, then canonicalize with merge_nodes//0. Only Id vars unify. Aliasing may instantiate variables inside Keys; the next merge collapses any collisions.
- unif/1 (semidet, impure by design): True for Eq=(A=B); performs A=B (no occurs-check). Intended only for rebuild//1 via exclude/3. Safe because Ids are fresh, acyclic logic variables.
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4 (nondet, pure): Example rewrite rules/helpers. Emit nodes/equalities only; avoid in-place rewrites; use Index to restrict search when possible. Must not inspect or bind Ids.
- extract/2, extract_node/1 (semidet, aliases Ids): Validation helpers used by extract//0. Intentionally alias Ids via member/2; validation only; discard any bindings afterwards.
- saturate/3 (det, driver): Worker that saturates with a step bound; rebuild index each iteration; only Ids may unify (in rebuild/merge). Fixpoint is length-based; alias-only steps do not count as progress.
- DCG bridging: Each DCG nonterminal compiles to extra-args; DCG forms remain pure producers. merge_nodes//0 is a DCG shim over merge_nodes/2.

Notes on mutable class Ids
- Class Ids are fresh logic variables that act as mutable, unique class identifiers. They alias via unification only; never compare them by name.
- Unifying Ids can instantiate variables embedded in Keys; always follow any aliasing with merge_nodes/2 (rebuild//1 already does this).

Equality and identity
- Key equality is determined after standard ordering and confirmed with (==), preserving variable identity.
- All effects are logical and backtrackable. Only Id variables unify; no occurs-check is needed because Ids are fresh, acyclic logic variables.

Notes
- Logic variables as class Ids are intentional: unification is the only mutating operation and is backtrackable. This can instantiate variables embedded in Keys; always follow Id aliasing with merge_nodes/2.
- Terminology: Ids are logic variables (not predicate symbols); they alias classes only via unification and should never be compared by name.
- Internal predicates are pure w.r.t. Keys; only Id variables may be unified, and only in rebuild//1 and merge_nodes/2.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Id, +Pairs) is semidet.
%  Read-only lookup of the Id for Key in a canonical ordset (exactly one Key-Id per Key).
%  Pre: Pairs must be canonical (sorted, deduplicated) as produced by merge_nodes/2.
%  Method: prunes by standard order; confirms identity with (==) to preserve variable identity.
%  Effects: binds only Id; fails if Key is absent; never unifies Keys or Ids; does not allocate.
%  Ids: fresh logic variables (mutable, backtrackable class identifiers); never compare by name.
%  Complexity: O(N) worst-case (with pruning).
%  Determinism: semidet; steadfast; pure.
%  Note: Non-canonical inputs can misidentify matches; call merge_nodes/2 first. Does not insert; use add_node/3 to create entries.
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
%  Insert Term and return its class Id; reuse the existing Id if Key already exists.
%  Compound: build Key = F(ChildIds) left-to-right (stable arg order ⇒ congruence).
%  Atom/var: Key = Term; preserves variable identity (no variant/alpha-renaming).
%  Emits only Key-Id items; never unifies Ids; duplicates are removed later by merge_nodes/2.
%  Pre: In is an ordset.
%  Ids: fresh logic variables as mutable class ids; alias only via unification; never compare by name.
%  Cost: build O(|Term|); insert O(N).
%  Determinism: det; steadfast; pure w.r.t. Keys.
%  Note: DCG form is a pure producer; no unification occurs here.
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
%  Ensure Node has a class Id; reuse if present, otherwise insert Node-Id with a fresh unbound Id.
%  In/Out are ordsets; prune by standard order; confirm with (==) to preserve variable identity.
%  No unification/canonicalization here; ord_add_element/3 preserves set semantics.
%  Pre: In is an ordset.
%  Effect: fresh Id only when Node is new; Out=In if Node already exists.
%  Ids: logic variables as mutable class ids; alias only via unification; never compare by name.
%  Cost: O(N) over |In|.
%  Determinism: det; quasi-pure (no Id unification).
%  Note: Keys never unify here; only set membership is checked.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%! union(+IdA, +IdB, +In, -Out) is det.
%  Alias classes by unifying IdA with IdB, then canonicalize via merge_nodes/2.
%  Requires: IdA/IdB are class Ids from this e-graph.
%  Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic variables.
%  Unification may instantiate variables inside Keys; the subsequent merge collapses any collisions.
%  Effects: only Id variables unify; Keys never do. Backtrackable.
%  Ids: logic variables as mutable class ids; never compare by name.
%  Determinism: det; logical effect (Id aliasing).
%  Note: Always follow aliasing with merge_nodes/2 (union//2 already does).
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG wrapper for merge_nodes/2. Emits nothing; only canonicalizes.
%  Determinism: det; steadfast.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize Nodes: keep exactly one Key-Id per Key; repeat until stable w.r.t. Id aliasing.
%  Out is canonical (sorted, one entry per Key).
%  Algorithm: sort/2 → group_pairs_by_key/2 → unify Ids within each group with the first; repeat if any group merged.
%  Unifying Ids may instantiate variables inside Keys; the next pass collapses any new collisions.
%  Cost: O(N log N) per pass; multiple passes possible.
%  Effects: only Id variables unify; Keys never do. Backtrackable.
%  Termination: number of distinct Id variables strictly decreases each merging pass.
%  Determinism: det; logical effects (Id unification only).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  For Key-[H|T], unify each Id in T with H; Changed=true iff T is nonempty.
%  Effects: only Id variables unify; Keys never do.
%  Note: Id unification may instantiate variables inside Keys; the next merge pass collapses collisions.
%  Cost: O(|T|).
%  Determinism: det; logical effects (Id unification).
%  Note: Does not change Keys; only the representative Id is propagated.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for +/2: from (A+B)-AB emit B+A-BA and AB=BA.
%  Models equality without in-place rewrite; emit exactly one commuted variant per match.
%  Notes: BA is fresh; equality is consumed by rebuild//1. Rules must not inspect or bind Ids; no side effects.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  Restrict to members of class(BC) via Index; emit at most one triple per match.
%  If class(BC) is absent, emit nothing.
%  Index: rbtree Id -> [Keys]; rebuilt each iteration; read-only here.
%  Notes: AB and ABC_ are fresh; unification deferred to rebuild//1. Rules must not inspect or bind Ids; no side effects.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC) with A fixed.
%  Emit at most one triple per qualifying member; confine rewrites to the class.
%  Notes: Pure producer; must not inspect or bind Ids.
%  Determinism: nondet over Members; tail-recursive.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of +/2: if class(B) contains integer 0, emit A=AB.
%  Use once/1 to avoid duplicates; match 0 exactly with (==).
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes: Unification happens in rebuild//1; rules must not inspect or bind Ids.
%  Determinism: semidet; pure producer.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums into a single constant.
%  Introduce C for VC is VA+VB and emit VC-C, C=AB.
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes: Uses is/2; preserves Prolog numeric type semantics; pure producer. Unification deferred to rebuild//1.
%  Determinism: nondet; must not inspect or bind Ids.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Pick numeric VA in class(A), then search class(B) for numeric VB.
%  Staged search avoids building pairs eagerly; guard with number/1.
%  Notes: Pure producer; unification deferred to rebuild//1.
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
%  Notes: number/1 guards are ensured by constant_folding_a//4. Pure producer; unification deferred to rebuild//1; must not inspect or bind Ids.
%  Determinism: nondet over numeric members of class(B); no side effects.
constant_folding_b([VB | BNodes], VA, AB, Index) -->
   (  {number(VB)}
   -> {VC is VA + VB},
      [VC-C, C=AB]
   ;  []
   ),
   constant_folding_b(BNodes, VA, AB, Index).
constant_folding_b([], _, _, _) --> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply each Rule(Node,Index)// to Node using Index; append outputs in rule order.
%  Rules is a list of callable DCG nonterminals of the form Rule(+Node,+Index)//.
%  Node is Key-Id; Rules may only emit Key-Id and (=)/2 items.
%  Implementation: uses library(dcg/high_order):sequence//2.
%  Index: rbtree Id -> [Keys]; rebuilt after any Id aliasing; read-only within rules.
%  Notes: Pure producer; steadfast; must not inspect or bind Ids (treat Ids as opaque).
%  Determinism: nondet over Rules; each Rule runs once per Node (node order, then rule order). No side effects.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Call a single DCG rule Rule(Node,Index)// on Node.
%  Notes: Pure producer; steadfast; must not inspect or bind Ids (Ids are opaque class variables).
%  Determinism: as Rule//2. No side effects.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build rbtree Index mapping Id -> [Keys] from canonical Nodes.
%  Pre: Nodes are canonical (use merge_nodes/2 first).
%  Rebuild after any Id aliasing (Ids are the map keys).
%  Ids: logic variables as mutable class ids; the variable itself is the key. Never compare by name.
%  Cost: O(N log N).
%  Determinism: det; pure; steadfast.
%  Note: Do not reuse across aliasing; rebuild immediately after any (=)/2 on Ids (e.g., via rebuild//1 or merge_nodes/2).
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist using Index; produce Matches (nodes and (=)/2).
%  Output order: worklist order, then per-node rule order.
%  Notes: Uses foldl/4 with rules//3; steadfast accumulator; rules must not inspect or bind Ids.
%  Cost: O(|Worklist|*|Rules| + |Matches|) plus per-Rule cost over Index.
%  Determinism: det; produces a concrete list; no mutation or Id unification. Pure.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to the DCG output in O(1) via difference lists.
%  Scheduling only; canonicalization is done by merge_nodes/2.
%  Notes: Idiomatic DCG trick: push_back(L), L --> []. Steadfast; does not inspect or bind Ids.
%  Determinism: det; pure producer; no side effects. Keys/Ids are not touched.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (nodes and (=)/2), then canonicalize:
%    - exclude(unif, Matches, NewNodes): perform A=B; drop equalities.
%    - push_back(NewNodes): enqueue Key-Id items.
%    - merge_nodes: dedupe and unify Id classes.
%  Effects: only Id aliasing via (=)/2; backtrackable.
%  Ids: logic variables as mutable class ids; aliasing may instantiate vars inside Keys.
%  Determinism: det; logical effects (Id unification only).
%  Note: Safe because only Id variables unify; Keys remain immutable.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Run Rules to a length-based fixpoint: repeat until rebuild/merge does not change list length.
%  SWI note: 'inf' is not numeric; on SWI call saturate(Rules, LargeInteger) or adjust the guard to accept 'inf'.
%  Determinism: det; Rules must be pure producers (emit only nodes/equalities). Alias-only steps do not count as progress.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run up to MaxSteps iterations (integer >= 0, or 'inf' where supported).
%  Fixpoint: stop when length is unchanged after rebuild/merge. Alias-only steps don't change length.
%  SWI note: MaxSteps must be an integer; 'inf' triggers a type_error.
%  Determinism: det.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker: rebuild Id->Keys index each iteration; stop on stable length or when MaxSteps runs out.
%  Rules must be pure producers; unification happens only in rebuild//1 and merge_nodes/2.
%  Ids: logic variables as mutable class ids; never compare by name; always rebuild the index after aliasing.
%  SWI note: MaxSteps must be an integer; use a large integer or adjust the guard to accept 'inf'.
%  Determinism: det driver; nondet only from Rules.
%  Note: Alias-only steps do not change length (by design).
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
%  True for Eq = (A=B); performs that unification as a side-effect.
%  Intended only for rebuild//1 via exclude/3.
%  Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic variables.
%  Ids: only Id variables should appear here; Keys must not be unified.
%  Determinism: semidet; impure by design (Id unification).
%  Note: Never call from rewrite rules; keep all unification centralized in rebuild//1.
unif(A=B) :- A=B.

%! extract(-Nodes) is semidet.
%  Validate and return Nodes.
%  Warning: aliases class Id variables via member/2; use for validation only.
%  To inspect without aliasing, use the node list directly.
%  Ids: logic variables; discard any bindings made here; never compare Ids by name.
%  Determinism: semidet; aliases Ids.
%  Note: This intentionally aliases Ids to witnesses; do not rely on bindings after return.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  Validate: every Id-class has at least one Key witness.
%  Warning: intentionally aliases Ids via member/2; prefer extract/1 in user code.
%! extract(+Nodes, -Nodes) is semidet.
%  Helper for extract//0; succeeds iff each Id-group is nonempty.
%  Warning: aliases Ids; discard any bindings afterwards.
%  Notes: Pure w.r.t. Keys; impurity comes only from aliasing Ids during validation.
%  Determinism: semidet; aliases Ids; pure w.r.t. Keys.
%  Note: Behavior relies on member/2 aliasing an Id with one of its Keys.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one Key; fails otherwise.
%  Warning: unifies each Id with one of its Keys via member/2 (validation only).
%  Notes: Intentionally aliases Ids; do not rely on any bindings produced.
%  Note: With Groups built from Nodes, groups are nonempty by construction; failure indicates a corrupted index.
%  Determinism: semidet; aliases Ids.
%  Note: The aliasing is deliberate to validate non-emptiness of classes; discard bindings after use.
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
%  Build right-associated sum 1+2+...+N (as a +(A,B) term chain). N >= 1.
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
%  Enumerate possible results R after saturating with all rules, then validate via extract//0. Uses distinct/1 (SWI‑Prolog) to remove duplicates.
%  Determinism: nondet over alternative extractions R.
example3(N, Expr, R) :-
   distinct(R, phrase((
      add(Expr, R),
      saturate([comm, assoc, reduce, constant_folding], N),
      extract
   ), [], _)).
