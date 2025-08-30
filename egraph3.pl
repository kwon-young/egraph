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
- lookup/2 (semidet, pure, steadfast): Return Id for Key from a canonical ordset. Prunes by standard order; confirms Key identity with (==). Binds only Id; fails if absent. Pre: canonical (merge_nodes/2). O(N).
- add//2, add/4 (det, pure w.r.t. Keys): Build Key = F(ChildIds) left‑to‑right (stable arg order ⇒ congruence) and emit Key-Id. Never binds Ids; duplicates are removed by merge_nodes/2. Pre: In is an ordset.
- add_node/4, add_node/3 (det, quasi‑pure): Ensure Node has a class Id in the ordset. Reuse if present; otherwise insert Node-Id with a fresh logic var. No canonicalization or Id unification.
- merge_nodes//0, merge_nodes/2 (det, logical effects): Canonicalize to one Key‑Id per Key: sort → group → unify group Ids with a representative; repeat while merges occur. Only Id vars unify; Keys never do. Terminates because the number of distinct Ids strictly decreases.
- merge_group/4 (det, logical effects): For Key-[H|T], unify each Id in T with H; Changed=true iff T \= []. Representative is H.
- make_index/2 (det, pure): Build rbtree Id→[Keys] from canonical Nodes. The rbtree key is the Id variable itself (by identity, not print-name). Rebuild after any Id aliasing. O(N log N). Keys stored as-is.
- rules//3, rule//3 (nondet, pure): Apply each DCG Rule(Node,Index)// to Node using Index. Rules may emit only Key‑Id items and (=)/2 equalities; must not inspect or bind Ids. Output order: per-node, then per-rule.
- match/4 (det, pure): Run Rules over Worklist using Index; collect Key‑Id items and (=)/2 equalities in Matches. No unification here. Output order follows worklist, then per-rule.
- push_back//1 (det, pure): Append a list to DCG output in O(1) via difference lists; scheduling only.
- rebuild//1 (det, logical effects): Apply (=)/2 equalities (alias Ids), enqueue Key‑Id items, then canonicalize (merge_nodes//0). Only Ids unify; Keys never do.
- unif/1 (semidet, impure by design): True for Eq=(A=B) and performs A=B (no occurs‑check). Intended only for rebuild//1 via exclude/3. Safe for fresh, acyclic Ids. Never call from rules.
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4 (nondet, pure): Example rewrite rules/helpers. Pure producers: emit nodes/equalities only; no in‑place rewrites; use Index to restrict search; must not inspect or bind Ids.
- extract/2, extract_node/1 (semidet, aliases Ids): Validation helpers for extract//0. Intentionally alias Ids via member/2; discard bindings after use.
- saturate/4 (det, driver): Iterate with a step bound. Rebuild the Id→[Keys] index each iteration; only Ids may unify (during rebuild/merge). Stop when length is unchanged; alias‑only steps do not count as progress.
- DCG bridging: DCG nonterminals expand to extra arguments and are pure producers. Note: merge_nodes//0 must delegate to merge_nodes/2; rebuild//1 assumes this DCG shim exists.

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
%  Return Id for Key from a canonical ordset of Key-Id pairs (read-only).
%  - Requires canonical input (see merge_nodes/2).
%  - Prunes by standard order; confirms exact Key identity with (==).
%  - Binds Id only; fails if absent; steadfast; no allocation on success.
%  Cost: O(N) worst case. Pure w.r.t. Keys/Ids; no backtracking on success.
%  Notes:
%  - Undefined on non-canonical input; canonicalize first.
%  - Ids are logic variables (class ids); compare by identity, never by print-name.
%  - Build Keys from compound terms with add/4 before inserting/searching.
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
%  Insert Term and return its class Id (reusing Id if an identical Key exists).
%  - compound: Key = F(ChildIds) built left-to-right (stable order ⇒ congruence)
%  - atom/var: Key = Term; variable identity is part of the Key (no variant renaming)
%  - Emits Key-Id only; never unifies Ids here. Duplicates removed by merge_nodes/2.
%  Pre: In is an ordset (canonical preferred).
%  Cost: build O(|Term|), insert O(N). Det; steadfast; pure on Keys.
%  Notes:
%  - Ids are logic vars (mutable class identifiers); the caller supplies the fresh Id.
%  - DCG form is a pure producer (no side effects).
%  - Keys are immutable data; only Id variables unify elsewhere.
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
%  Ensure Node has a class Id in the ordset.
%  - If present: reuse Id and Out=In; otherwise insert Node-Id using the fresh Id variable provided by the caller.
%  - Uses standard order and (==) to respect variable identity; no canonicalization here.
%  - No Id unification; ord_add_element/3 preserves set semantics.
%  Pre: In is canonical (from merge_nodes/2). Ids are logic vars (class ids).
%  Cost: O(N). Det; quasi-pure (introduces at most one fresh Id variable; no Id unification).
%  Notes:
%  - Canonicalize via merge_nodes/2 before calling.
%  - add_node/3 (Node-Id, In, Out) is a thin wrapper over add_node/4.
%  - Compare Ids by identity (the variable), not by print-name.
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
%  - Only Id variables unify; Keys never do. Unifying Ids may instantiate variables inside Keys; the next merge collapses collisions.
%  - Uses (=)/2 (no occurs-check); safe for fresh, acyclic Id vars. Backtrackable.
%  Determinism: det; logical effects (Id aliasing only).
%  Notes:
%  - Pass only class Id variables; never unify Keys directly.
%  - Always follow with merge_nodes/2 (union//2 already does this).
%  - Ids are logic variables acting as mutable unique identifiers.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG shim for merge_nodes/2; emits nothing; only canonicalizes.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize to one Key-Id per Key; iterate to a fixpoint under Id aliasing.
%  - sort/2 → group_pairs_by_key/2 → unify each group's Ids with the first; repeat while any group has length > 1.
%  - Only Id vars unify; Keys never do. Id unification may instantiate variables inside Keys; the next pass collapses collisions.
%  - Cost: O(N log N) per pass; repeats until stable. Det.
%  Notes:
%  - Terminates because the number of distinct Id vars strictly decreases on any merge.
%  - Representative Id per Key is the first after sorting (backtrackable; not stable across runs).
%  - Rebuild any Id→[Keys] index after calling (Ids may have aliased).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  For Key-[H|T], unify each Id in T with H; Changed=true iff T \= [].
%  - Only Id vars unify; Keys unchanged. Representative Id is H.
%  Cost: O(|T|). Det.
%  Notes:
%  - Id unification can instantiate variables embedded in Keys indirectly.
%  - Changed is an accumulator flag for merge_nodes/2 (detects progress).
%  - Uses (=)/2 via maplist(=(H), T); no occurs-check; safe for fresh Ids.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity of +/2: from (A+B)-AB emit B+A-BA and AB=BA.
%  - Models equality without in-place rewrite; emit at most one commuted variant per match.
%  Notes:
%  - BA is fresh; the equality is consumed by rebuild//1 (Id unification only).
%  - Rules must not inspect or bind Ids; only emit nodes and (=)/2 between Ids.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restrict to members of class(BC) via Index; emit at most one triple per match.
%  Index: rbtree Id -> [Keys]; rebuilt each iteration; read-only.
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
%  - Uses once/1 to avoid duplicates; match 0 exactly with (==).
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Unification happens in rebuild//1 (Ids only); rules must not inspect or bind Ids.
%  - Checks numeric 0 with (==) to avoid arithmetic coercions.
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
%  - Uses is/2; respects Prolog numeric semantics; pure producer.
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
%  - Pure producer; unification deferred to rebuild//1 (Ids only); must not inspect or bind Ids.
%  Determinism: nondet over numeric members of class(B); no side effects.
%  The emitted VC-C is a new Key-Id pair; equality C=AB is consumed by rebuild//1.
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
%  - Rules is a list of callable DCG nonterminals Rule(+Node,+Index)//.
%  - Node is Key-Id; rules may only emit Key-Id and (=)/2 items.
%  Impl: library(dcg/high_order):sequence//2. Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Pure producer; steadfast; must not inspect or bind Ids.
%  - Output order: per-node, then per-rule. Do not rely on representative Ids.
%  - Rules are independent; side effects happen only in rebuild//1 (Id aliasing).
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Call a single DCG rule Rule(Node,Index)// on Node.
%  Notes:
%  - Pure producer; steadfast; must not inspect or bind Ids.
%  - Determinism follows Rule//2. Kept separate for clarity with sequence//2.
%  - Thin wrapper to adapt sequence//2 calling convention.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build rbtree Index mapping Id -> [Keys] from canonical Nodes.
%  - Pre: Nodes must be canonical (merge_nodes/2).
%  - Rebuild after any Id aliasing (Ids are the map keys).
%  Ids are logic variables (mutable class ids); the variable itself is the key. Never compare by print-name.
%  Note: rbtree uses standard order; variable identity (not print-name) orders keys.
%  Cost: O(N log N). Det; pure; steadfast.
%  Impl: transpose_pairs/2 flips Key-Id to Id-Key; Keys are stored as-is (no unification).
%  Notes:
%  - Intended for the current iteration only; rebuild after union/rebuild.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist using Index; produce Matches (nodes and (=)/2).
%  - Output order: worklist order, then per-node rule order.
%  Impl: foldl/4 with rules//3; steadfast accumulator.
%  Cost: O(|Worklist|*|Rules| + |Matches|) plus per-Rule cost over Index.
%  Determinism: det; produces a concrete list; no mutation or Id unification. Pure.
%  Notes:
%  - Matches are scheduled only; side effects happen later in rebuild//1.
%  - Worklist is typically the current canonical Nodes.
%  - Index is read-only; rebuild whenever Ids may have aliased.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to DCG output in O(1) via difference lists.
%  - Scheduling only; canonicalization is done by merge_nodes/2.
%  Notes:
%  - Idiomatic DCG trick: push_back(L), L --> [].
%  - Steadfast; does not inspect or bind Ids; no side effects.
%  - Structural only; does not touch Keys or Ids.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (nodes and (=)/2), then canonicalize:
%    - exclude(unif, Matches, NewNodes): perform A=B; drop equalities.
%    - push_back(NewNodes): enqueue Key-Id items.
%    - merge_nodes: dedupe and propagate Id aliasing.
%  Effects: only Id aliasing via (=)/2; backtrackable. May instantiate vars inside Keys.
%  Determinism: det; logical effects (Id unification only). Equalities must be between class Ids.
%  Notes:
%  - Always follow Id aliasing with merge_nodes/2 to rebuild representatives (done here).
%  - Never include Key=Key or Key=Id equalities; only class Ids may appear in (=)/2.
%  - Rebuild any Id→[Keys] index after this step (see make_index/2).
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Run Rules to a length-based fixpoint: repeat until length is unchanged after rebuild/merge.
%  Determinism: det. Rules must be pure producers (only emit nodes/equalities). Alias-only steps do not count as progress.
%  Portability: Delegates to saturate/2 with MaxSteps=inf. On systems where atoms and numbers cannot be compared arithmetically, use a large integer instead.
%  Notes:
%  - The fixpoint ignores pure aliasing steps that do not add/remove pairs.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run up to MaxSteps iterations.
%  - MaxSteps: integer >= 0. 'inf' allowed only if it compares with numbers on your Prolog; otherwise pass a large integer.
%  - Stop when length is unchanged after rebuild/merge. Alias-only steps don't change length.
%  Determinism: det.
%  Notes:
%  - Use a large integer instead of 'inf' where atoms and numbers are not arithmetically comparable.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Driver: rebuild the Id->Keys index each iteration; stop on stable length or when MaxSteps runs out.
%  - Rules must be pure producers; unification happens only in rebuild//1 and merge_nodes/2.
%  - Ids are logic vars; rebuild the index after aliasing; never compare by print-name.
%  - If MaxSteps='inf', the guard (N > 0) requires a Prolog where 'inf' compares with numbers; otherwise use a large integer.
%  Determinism: det driver; nondet only from Rules.
%  Notes:
%  - Progress metric is length only; pure aliasing steps are invisible to the stop test.
%  - Worklist per step is the current canonical Nodes (Index is rebuilt every iteration).
%  - Ids are mutable only via unification; treat them as opaque identity tokens.
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
%  - Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic logic variables.
%  - Only Id variables should appear here; Keys must not be unified.
%  Determinism: semidet; deliberately impure (Id unification). Do not call from rewrite rules.
%  Notes:
%  - The only place outside merge_nodes/2 where Ids are explicitly unified on purpose.
%  - Keep Keys as pure data; never construct Eq with Keys.
unif(A=B) :- A=B.

%! extract(-Nodes) is semidet.
%  Validate and return Nodes (aliases Ids).
%  - Aliases class Id variables via member/2; for validation only.
%  - To inspect without aliasing, use the node list directly.
%  Ids: logic variables; discard any bindings produced here.
%  Determinism: semidet.
%  Notes:
%  - Intentionally aliases Ids; do not use in normal rewriting or production code.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  Validate: every Id-class has at least one Key witness.
%  Warning: intentionally aliases Ids via member/2; prefer extract/1 in user code.
%! extract(+Nodes, -Nodes) is semidet.
%  Helper for extract//0; succeeds iff each Id-group is nonempty.
%  - Aliases Ids; discard any bindings afterwards. Pure w.r.t. Keys.
%  Determinism: semidet.
%  Notes:
%  - Fails only if the index is corrupted (should not happen with merge_nodes/2).
%  - Side-effect is intentional (Id aliasing); do not keep bindings.
%  - For tests/validation; do not rely on the bindings it creates.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one Key; fails otherwise.
%  - Unifies each Id with one of its Keys via member/2 (validation only).
%  - With Groups built from Nodes, groups are nonempty by construction; failure indicates a corrupted index.
%  Determinism: semidet; aliases Ids; discard bindings after use.
%  Notes:
%  - Intentionally aliases Ids; use only in tests/validation.
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
