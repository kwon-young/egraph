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
- extract//0 and extract/1 alias Ids via member/2 to choose a concrete representative term per class; use them as the final step of an e-graph pipeline. To inspect without aliasing, examine the Nodes list directly.

Public API
- add//2, union//2, saturate//1, saturate//2, extract/1, extract//0.

Implementation predicates (quick reference)
- lookup/2 (semidet, pure, steadfast): On canonical Pairs, find Id for Key by standard-order pruning then (==) confirmation. Binds Id only; never constructs/unifies Keys or allocates Ids. Pre: canonical (merge_nodes/2). Cost: O(N).
- add//2, add/4 (det, pure wrt Keys): Build Key=F(ChildIds) left-to-right (stable congruence) and emit only Key-Id. No Id unification; duplicates removed by merge_nodes/2. Pre: In is an ordset.
- add_node/4, add_node/3 (det, quasi-pure): Ensure Node has a class Id; reuse if present, else insert Node-Id with a fresh Id var. No canonicalization or Id unification. Pre: In canonical.
- merge_nodes//0, merge_nodes/2 (det, Id effects only): Canonicalize to one Key-Id per Key (sort -> group -> unify group Ids with the first); repeat to a fixpoint. Keys never unify. Terminates because the number of distinct Ids strictly decreases.
- merge_group/4 (det, Id effects only): For Key-[H|T], unify all Ids in T with H; Changed=true iff T\=[] (representative is H).
- make_index/2 (det, pure): Build rbtree Id->[Keys] from canonical Nodes (Id variables are keys by identity). Rebuild after aliasing. Cost: O(N log N).
- rules//3, rule//3 (nondet, pure): Apply each Rule(Node,Index)// to Node. May emit only Key-Id and (=)/2 between Ids; must not inspect/bind Ids. Output: per-node, then per-rule.
- match/4 (det, pure): Run Rules over Worklist using Index; produce scheduled Matches (Key-Id and (=)/2). No unification here. Output order: worklist, then per-rule.
- push_back//1 (det, pure): Append a list to DCG output in O(1) via difference lists; scheduling only.
- rebuild//1 (det, Id effects only): Apply (=)/2 equalities (alias Ids), enqueue new nodes, then canonicalize (merge_nodes/2).
- unif/1 (semidet, intentionally impure): True for Eq=(A=B); performs A=B (no occurs-check). Only for rebuild//1 via exclude/3. Safe for fresh, acyclic Ids. Never call from rules.
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4 (nondet, pure): Example rewrite rules/helpers. Pure producers; consult Index only; never inspect/bind Ids; no in-place rewrites.
- extract/2, extract_node/1 (semidet, aliases Ids): Extraction helpers for extract//0. They unify each class Id with a concrete Key via member/2; use as the final step and discard bindings if you must continue analysis.
- saturate/4 (det, driver): Iterate with a step bound. Rebuild Id->[Keys] each iteration; only Ids may unify (during rebuild/merge). Stop when length is unchanged; alias-only steps are not progress.
- DCG bridging: DCG calls to merge_nodes//0 expand to merge_nodes/2; no extra wrapper required on SWI-Prolog. Nonterminals must remain pure producers.
- Id discipline: Ids are fresh logic variables acting as mutable class identifiers. Alias via unification only; compare by identity (==), never by name/print-name.

Notes on mutable class Ids
- Class Ids are fresh logic variables (not predicate symbols) that act as mutable, unique class identifiers. They alias via unification only; never compare them by print-name.
- Unifying Ids can instantiate variables embedded in Keys; always follow aliasing with merge_nodes/2 (rebuild//1 already does this).

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
%  Find Id for Key in a canonical ordset of Key-Id pairs.
%  - Pre: Pairs canonicalized by merge_nodes/2.
%  - Algo: prune by standard order; confirm with (==). Binds Id only; never constructs/unifies Keys.
%  - Determinism/Complexity: semidet; steadfast; O(N). No choicepoints on success.
%  Notes:
%  - On non-canonical input, may fail spuriously.
%  - Ids are fresh logic vars used as mutable class ids; compare by identity (==) only.
%  - Keys preserve variable identity (built by add/4).
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
%  Build Key for Term and ensure a Node-Id exists; return Id of its class.
%  - Compound Term: Key = F(ChildIds) (left-to-right ⇒ stable congruence).
%  - Atom/var Term: Key = Term (variable identity is part of the Key).
%  - Emits only Key-Id; never unifies Ids. Deduplication is done by merge_nodes/2.
%  Pre: In is an ordset (preferably canonical).
%  Determinism/Complexity: det; steadfast; pure wrt Keys. Build O(|Term|); insertion O(N) via ord_add_element/3.
%  Notes:
%  - Reuses existing Id if present; otherwise creates a fresh Id.
%  - DCG form is a pure producer (no id aliasing).
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
%  Ensure Node-Id is present in canonical ordset In; produce Out.
%  - If present: reuse Id, Out=In; else insert Node-Id with a fresh Id.
%  - Uses standard order and (==) on Keys (preserves variable identity); no canonicalization here.
%  - Never unifies Ids; ord_add_element/3 enforces set semantics.
%  Pre: In is canonical.
%  Determinism/Complexity: det; O(N). Quasi‑pure (may allocate one fresh Id).
%  Notes:
%  - Out remains canonical.
%  - Compare Ids by identity (==) only.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%! union(+IdA, +IdB, +In, -Out) is det.
%  Alias classes by unifying IdA with IdB, then canonicalize.
%  - Only Id vars unify; Keys never do. This may instantiate vars inside Keys; merge_nodes/2 collapses collisions.
%  - Uses (=)/2 (no occurs-check); safe for fresh, acyclic Ids. Backtrackable.
%  Det: det. Side effect: Id aliasing only (backtrackable).
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG call to merge_nodes/2; emits nothing. Pure producer.
%  Note: On SWI-Prolog, DCG expansion calls merge_nodes/2 directly.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize Nodes to at most one Key-Id per Key; iterate until stable.
%  - Steps: sort -> group_pairs_by_key -> unify all Ids in each group with the first (representative).
%  - Only Id vars unify; Keys never do. Id aliasing may instantiate vars inside Keys; the next pass collapses collisions.
%  Complexity: O(N log N) per pass; repeats while merges occur.
%  Notes:
%  - Out is canonical (sorted; one Key-Id per Key).
%  - Terminates: merges strictly decrease the number of distinct Id vars.
%  - Representative Id is the first after sorting; do not rely on it across backtracking.
%  - Rebuild any Id→[Keys] index after this (Ids may have aliased).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  For Key-[H|T], unify all Ids in T with H; Changed=true iff T \= [].
%  - Only Id vars unify; Keys unchanged. Representative Id is H.
%  Complexity: O(|T|). det.
%  Notes:
%  - Id unification may instantiate variables embedded in Keys (collapsed in next pass).
%  - Keys never unify; only Ids may alias.
%  - Changed is the progress flag for merge_nodes/2.
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
%  - BA is fresh; equality is consumed by rebuild//1 (Id aliasing only).
%  - Rules must not inspect or bind Ids; only emit nodes and (=)/2 between Ids.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restrict to members of class(BC) via Index; emit at most one triple per match.
%  Index: rbtree Id -> [Keys]; rebuilt each iteration; read-only.
%  - If BC is absent from Index, the rule emits nothing.
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
%  - Use strict term equality (==) to match numeric 0; avoids arithmetic coercion.
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
%  Apply Rules to Node using Index; append outputs in rule order. Each Rule is a DCG nonterminal Rule(Node,Index)//.
%  - Node is Key-Id; rules may emit only Key-Id items and (=)/2 between Ids.
%  - Uses sequence//2 from library(dcg/high_order). Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Pure producer; steadfast; Ids are opaque mutable identifiers (do not inspect/bind).
%  - Output order: per-node, then per-rule. Do not rely on representative Ids.
%  - Rules are independent; side effects happen only in rebuild//1 (Id aliasing).
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Invoke Rule(Node,Index)// on Node.
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
%  - Ids are logic vars (mutable class ids); keyed by variable identity (==), not by name.
%  Complexity/Determinism: O(N log N); det; pure; steadfast.
%  Impl: transpose_pairs/2 flips Key-Id to Id-Key; Keys are stored as-is (no unification).
%  Notes:
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
%  Append List to DCG output in O(1) (difference lists).
%  - Scheduling only; merge_nodes/2 does canonicalization.
%  Notes:
%  - Idiomatic DCG trick: push_back(L), L --> [].
%  - Pure wrt Keys/Ids; no side effects.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (Key-Id items and (=)/2 between Ids), then canonicalize:
%    - exclude(unif, Matches, NewNodes): perform Id aliasing (A=B) and drop equalities.
%    - push_back(NewNodes): enqueue Key-Id items.
%    - merge_nodes: dedupe; propagate effects of Id aliasing.
%  Effects: only Id aliasing; may instantiate variables inside Keys (collapsed on merge).
%  Determinism: det. Equalities must be between Ids (A and B are Id vars).
%  Notes:
%  - Rebuild any Id->[Keys] index after this (Ids are the map keys).
%  - Keys must never appear on the left/right of (=)/2 here.
%  - DCG call merge_nodes expands to merge_nodes/2.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Iterate Rules to a length fixpoint (after rebuild/merge).
%  - Rules are pure producers (emit only Key-Id and (=)/2).
%  - Alias-only steps are ignored (no change in length).
%  Portability: wraps saturate//2 with MaxSteps=inf; if your system lacks inf, call saturate//2 with a large integer.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run up to MaxSteps iterations; stop early when length stabilizes after rebuild/merge.
%  - MaxSteps: integer >= 0 (or inf where supported).
%  - Alias-only steps do not count as progress.
%  Determinism: det.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Driver. Each iteration: build Index, apply Rules over Nodes, rebuild (aliases Ids), then merge.
%  - Only rebuild//1 and merge_nodes/2 may unify Ids.
%  - Ids are logic vars (mutable); rebuild Index after aliasing; never compare by name/print-name.
%  - MaxSteps: integer >= 0; use a large integer if inf is unsupported.
%  Determinism: det. Nondet comes only from Rules.
%  Notes:
%  - Progress is measured by list length; alias-only steps are ignored.
%  - Worklist per step is the current canonical Nodes.
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
%  Succeeds for Eq=(A=B) and performs that unification (side effect).
%  Only called from rebuild//1 via exclude/3; never call from rules or user code.
%  - Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic logic variables.
%  - Only Id variables should appear here; Keys must not be unified.
%  Determinism: semidet; intentionally impure (Id unification).
%  Notes:
%  - The only place outside merge_nodes/2 where Ids are explicitly unified on purpose.
%  - Mutable Ids are logic variables (not predicate symbols); aliasing happens here or in merge_nodes/2 only.
unif(A=B) :- A=B.

%! extract(-Nodes) is semidet.
%  Final extraction: unify each class Id with one of its Keys to obtain concrete Prolog terms.
%  This is the last standard step when using an e-graph.
%  Side effects: aliases Ids (on purpose). Discard these bindings to continue analysis; to inspect without aliasing, look at Nodes directly.
%  Determinism: semidet.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  DCG wrapper for extraction (aliases Ids). This is the last standard step to obtain concrete terms.
%  Succeeds iff every class has at least one Key; otherwise fails.
%  Prefer extract/1 outside DCGs.
%! extract(+Nodes, -Nodes) is semidet.
%  Implementation of extract//0: for each Id->[Keys], unify Id with one Key to materialize a concrete representative.
%  This is the last standard step; it aliases Ids. Do not continue rewriting with these bindings.
%  Determinism: semidet. Fails only if a class has no Keys (should not happen after merge_nodes/2).
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  For each Id->[Keys] group, unify Id with one of its Keys; fails on an empty group.
%  Chooses concrete representatives (aliases Ids); core of extraction.
%  With Groups from Nodes, groups are nonempty by construction; failure indicates a corrupted index.
%  Determinism: semidet; aliases Ids. Perform extraction only as the final step.
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
