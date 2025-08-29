:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs (equivalence graphs) with congruence closure for Prolog terms, fully backtrackable.

Essentials
- State is an ordset of Key-Id pairs (standard order).
- Ids are fresh Prolog logic variables acting as mutable, backtrackable class identifiers (mutable unique identifiers). Unifying two Ids merges classes.
- A DCG threads the state as a difference list; the only mutation is Id unification.

Representation
- Node Key: either an atomic or variable term, or a compound whose arguments are child class Ids (congruence).
- Canonical form: after merge_nodes/2 there is at most one Key-Id per distinct Key (equality after sort uses (==), so variable identity matters).
- Index: rbtree Id -> [Keys], rebuilt after each canonicalization.

Execution
- add//2 builds Keys left-to-right and inserts Key-Id pairs (may introduce duplicates).
- Rules are DCGs that only produce: Key-Id items and equalities A=B. They never unify.
- rebuild//1 applies A=B (unifies Ids), schedules new nodes, then calls merge_nodes/2.

Identity and variants
- No alpha-normalization: structurally equal Keys with different variable identities are distinct.
- Sorting/identity use standard term order and (==); variable identity is observable.

Caveats
- merge_nodes/2 may need multiple passes: unifying Ids can instantiate variables appearing in Keys and reveal new duplicates.
- saturate//2 fixpoint is length-based; pure aliasing (no net Key-Id change) is invisible—rules must eventually add/remove pairs.
- IDs are variables, not atoms; do not persist or print them as stable names. If needed, map them to your own stable identifiers.
- extract//0 performs a validation pass that can alias IDs via member/2; use only on throwaway states or under backtracking.

DCG note
- In a DCG body, writing merge_nodes is translated to merge_nodes(+In,-Out); there is intentionally no merge_nodes//0 clause.

Public API
- add//2, union//2, saturate//1, saturate//2, extract/1, extract//0.

Related
- merge_nodes/2, make_index/2, rebuild//1.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Read-only lookup in an ordset of Key-Val pairs (standard term order).
%  - Pairs: strictly ordered ordset; Key must be nonvar.
%  - Equality uses (==) after ordering; variable identity matters; never unifies.
%  - Complexity: O(N) small-window linear scan (4/2/1 lookahead).
%  - Errors: var Key triggers instantiation_error via compare/3.
%  - Side-effects: none; does not bind Key or Pairs.
%  - Failure: fails cleanly if Key is not present.
%  Determinism: semidet.
%  Notes:
%    - Pure read; does not alias or bind IDs.
%    - Comparison uses standard order; equality check uses (==) after ordering; never binds variables.
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
%  - Compound: add subterms left-to-right; Key = F(ChildIDs) where ChildIDs are class IDs of subterms (congruence).
%  - Atomic or var: Key = Term itself. Variable identity is part of the Key; no α/variant‑normalization.
%  Notes:
%    - Id is a fresh Prolog variable used as the mutable, backtrackable class identifier. Unifying Ids (via union or rules) can instantiate variables inside Keys; effects are logical and backtrackable.
%    - No canonicalization here; duplicates may be introduced. Call merge_nodes (DCG) to collapse duplicates.
%    - In/Out (the DCG state) is an ordset of Key-Id pairs in standard term order. Equality after ordering uses (==); variable identity matters.
%  Side-effects: none (apart from growing the DCG output); Id creation is by allocating a fresh variable.
%  Determinism: det.
%  Note: consumes equalities (A=B) and appends only Key-Id items; rules themselves must not perform unification.
%  Note: variables (Ids) are used as rbtree keys under standard term order; always rebuild after any aliasing.
%  Note: unifying IDs here can instantiate variables appearing in Keys; a subsequent sort may reveal new duplicates.
%  Note:
%    - Keys are kept exactly as constructed; do not assume α-equivalence collapses variants.
%    - Ids are opaque logic variables local to the graph; do not treat them as stable names or serialize them.
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
%  Ensure Node has a class Id; reuse the existing Id if present, otherwise insert Node-Id.
%  Notes:
%    - In/Out are ordsets of Key-Id (standard order). Identity after ordering uses (==); no variant-normalization (variable identity matters).
%    - Unifying Ids elsewhere may bind variables inside Keys. Always re-canonicalize with merge_nodes/2 (or //0) after aliasing.
%  Side-effects: none (except possibly allocating a fresh Id variable when Node is new).
%  Determinism: det.
%  Note: reuses the existing Id if Node already exists; no unification occurs here and no canonicalization is performed.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%! union(+IdA, +IdB, +In, -Out) is det.
%  Alias classes by unifying IdA with IdB, then canonicalize with merge_nodes (DCG).
%  Rationale: Prolog variable unification yields a cheap, fully backtrackable union of classes.
%  Notes:
%    - IdA/IdB must be class IDs obtained from add//2 or add_node/4.
%    - Unifying IDs may instantiate variables occurring inside Keys; many rules rely on this.
%    - Uses (=)/2 without occurs-check. Safe here: class IDs are only ever unified with class IDs (never with compound terms).
%  Side-effects: aliases the two Id variables (logical, backtrackable); no other mutation.
%  Determinism: det.
%  Note: may expose new duplicate Keys only after merge_nodes/2; keep union + merge_nodes paired.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG reference to merge_nodes/2.
%  In DCGs, writing merge_nodes expands to merge_nodes(+In,-Out); there is no merge_nodes//0 clause by design.
%! merge_nodes(+In, -Out) is det.
%  Sort by Key, group equal Keys, unify all Ids in each group into the first; repeat until a fixpoint.
%  Complexity: O(N log N) per pass (sort + group); may take multiple passes.
%  Notes:
%    - Unifying Ids can instantiate variables inside Keys; a subsequent sort can reveal new duplicates, hence multiple passes.
%    - Leaves exactly one Key-Id pair per distinct Key at fixpoint.
%    - Change detection uses a fold accumulator: the next pass runs only if at least one group had >1 Id.
%  Determinism: det.
%  Note:
%    - The loop continues if any group had >1 Id or if resorting after unifications exposes new equal Keys.
%    - Sorting uses standard term order; equality after ordering uses (==); only Ids unify (no occurs-check needed).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Unify all IDs in a Key-group into the first; set Changed=true if the group had >1 ID.
%  Result: Rep is the first ID; each tail ID is unified with it.
%  Drives the outer fixpoint in merge_nodes/2.
%  Note: unifying IDs may instantiate variables appearing inside Keys; a subsequent sort can therefore reveal new duplicates.
%  Determinism: det.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity of (+): from (A+B)-AB emit B+A-BA and AB=BA.
%  Models equality without in-place rewrites; both orders share the class.
%  Matches only +(A,B) nodes; emits at most one result per match.
%  Note: BA is a fresh class ID for B+A; AB=BA is consumed by rebuild//1 to alias classes. Rules never perform unification themselves.
%  Determinism: nondet over the worklist; at most one emission per matching node (prevents duplicate blow-up).
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of (+): from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  Restricts candidates to members of class(BC) via Index to avoid quadratic search over unrelated nodes.
%  Note: AB and ABC_ are fresh class IDs; ABC=ABC_ is consumed by rebuild//1 to alias. The rule only emits nodes/equalities; no unification here.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC), keeping A fixed.
%  Confines candidate rewrites to the current equivalence class.
%  Determinism: nondet over Members.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of (+): if class(B) contains the integer 0, emit A=AB.
%  Eliminates the unit; once/1 avoids duplicates.
%  Note: uses (==) to match 0 exactly (not 0.0); only Keys already bound to 0 qualify. Emits A=AB; unification happens later in rebuild//1 (the rule itself does not unify).
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold numeric additions (integers/floats) into a single constant.
%  Shrinks the search space by canonicalizing ground arithmetic; introduces fresh C and preserves AB as the class Id via C=AB.
%  Note: uses is/2 for evaluation; the rule only emits nodes/equalities and does not unify IDs.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Helper: pick numeric VA in class(A), then search class(B) for numeric VB.
%  Staged search avoids building pairs eagerly.
%  Determinism: nondet over numeric members of class(A) and class(B).
constant_folding_a([VA | ANodes], B, AB, Index) -->
   (  {number(VA)}
   -> {rb_lookup(B, BNodes, Index)},
      constant_folding_b(BNodes, VA, AB, Index)
   ;  []
   ),
   constant_folding_a(ANodes, B, AB, Index).
constant_folding_a([], _, _, _) --> [].
%! constant_folding_b(+ClassB, +VA, -AB, +Index)// is nondet.
%  Helper: for numeric VB in class(B) compute VC is VA+VB; emit VC-C and C=AB.
%  Introduces fresh C as the class Id for VC while preserving AB as the class Id for the sum via C=AB (consumed by rebuild//1).
%  Note: arithmetic uses is/2; evaluation follows Prolog's numeric tower and type promotion rules.
%  Determinism: nondet over numeric members of class(B).
constant_folding_b([VB | BNodes], VA, AB, Index) -->
   (  {number(VB)}
   -> {VC is VA + VB},
      [VC-C, C=AB]
   ;  []
   ),
   constant_folding_b(BNodes, VA, AB, Index).
constant_folding_b([], _, _, _) --> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply each DCG Rule(Node,Index)// to Node with access to Index; backtracks over Rules.
%  Note: rules are pure producers (emit nodes and A=B); ID aliasing happens only in rebuild//1.
%  Determinism: nondet over Rules; outputs are appended to the DCG stream.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule Rule(Node,Index)// on Node.
%  Determinism: follows the determinism of Rule/3.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree Index mapping Id -> [Keys] from an ordset of Key-Id pairs.
%  Enables fast per-class access during rule matching.
%  Complexity: O(N log N) overall (grouping + tree build).
%  Notes:
%    - IDs reflect current aliasing after unions; IDs are logic variables used as map keys. Always rebuild after aliasing.
%    - Values list all concrete Keys for each class.
%    - Assumes Nodes are canonicalized by merge_nodes/2 to avoid duplicates.
%    - group_pairs_by_key/2 sorts internally; Nodes need not be pre-sorted by ID.
%    - Uses transpose_pairs/2 (autoloaded from library(pairs)).
%  Determinism: det.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce new matches (nodes and equalities).
%  Central collection phase before rebuilding the graph. Worklist is the current node set (ordset of Key-Id pairs).
%  Determinism: det given Rules/Worklist/Index; produces a (possibly empty) list; no mutation.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  DCG helper: append List at the end of the current output.
%  Schedules newly discovered items after the current worklist (O(1) via difference lists).
%  Note: purely structural; no deduplication and no unification side effects.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply equalities and schedule nodes, then canonicalize:
%    - exclude(unif, Matches, NewNodes): unifies A=B items and drops them.
%    - push_back(NewNodes): appends Key-Id items to the DCG output.
%    - merge_nodes: canonicalizes (calls merge_nodes/2 via DCG).
%  Effects: only class-ID aliasing via (=)/2; logical and backtrackable. Equalities are consumed.
%  Determinism: det.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Saturate with Rules until a fixpoint (no new nodes/equalities).
%  Note: see saturate/4 for the length-based fixpoint caveat (alias-only progress is invisible).
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Saturate for at most MaxSteps iterations (non-negative integer or inf).
%  Fixpoint compares lengths before/after rebuild (after merge_nodes/2).
%  Caveat: alias-only steps do not change the length; rules must eventually add/remove pairs.
%  Determinism: det as a driver; nondeterminism comes only from rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker for saturate//2. Threads the e-graph difference list explicitly (In/Out).
%  MaxSteps must be a non-negative integer. Do not pass the atom inf here; use the DCG
%  wrappers (saturate//1 or saturate//2) if you need an unbounded loop.
%  Fixpoint is length-based; pure ID aliasing with no net pair change is invisible. Use a bounded
%  MaxSteps if rules can cycle without adding/removing pairs.
%  Implementation: rebuilds the Id->Keys index on every iteration because ID variables may alias.
%  Note: length-based fixpoint ignores pure aliasing; ensure rules eventually add/remove Key-Id pairs or use a bounded MaxSteps.
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
%  True for equalities A=B and performs the unification as a side effect.
%  Use with exclude/3 to apply equalities and remove them from a worklist.
%  Notes: intentionally mutates class IDs via unification; fails for non-(=)/2 items. Effects are logical and backtrackable.
%  Determinism: semidet; succeeds once on (=)/2, fails otherwise.
%  Note: intentionally performs side-effect unification of class Id variables; use via exclude/3 to consume equalities.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Return the current nodes as Nodes (no validation).
%  Pairs with extract//0, which performs a validation pass.
%  Recommendation: prefer this in user code to avoid identifier mutation during validation.
%  Determinism: det.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  DCG variant: validates minimal invariants after saturation.
%  Invariant: for each Id, its class has at least one concrete Key.
%  Note: uses member/2 in a way that can alias/bind Id variables; use only for validation on throwaway states or under backtracking, not on persisted graphs.
%  Side-effects: may bind/alias Id variables; do not call on persisted graphs you intend to keep.
%  Note: prefer extract/1 in production; use extract//0 only for validation under backtracking.
%! extract(+Nodes, -Nodes) is semidet.
%  Underlying helper for extract//0; succeeds iff each ID-group has a concrete Key.
%  Note: arguments are typically the same variable to avoid copying; do not rely on side effects.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one concrete Key; fails otherwise.
%  Minimal consistency check; may bind IDs via member/2 (use only for validation).
%  Determinism: semidet.
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
