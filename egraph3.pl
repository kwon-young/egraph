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
- lookup/2 (semidet, pure, steadfast): Read-only Id lookup in a canonical ordset (one Key-Id per Key). Prunes by standard order; confirms identity with (==). Binds only Id; fails if Key absent. Precondition: canonical ordset.
- add//2, add/4 (det, pure w.r.t. Keys): Build Key=F(ChildIds) left-to-right (stable arg order ⇒ congruence). Emit only Key-Id items; no unification or canonicalization; duplicates are removed by merge_nodes/2.
- add_node/4, add_node/3 (det, quasi-pure): Ensure Node has a class Id; reuse if present, else insert Node-Id with a fresh, unbound Id variable. Inputs/outputs are ordsets. No canonicalization; no Id unification.
- merge_nodes//0, merge_nodes/2 (det, logical effects): Deduplicate to one Key-Id per Key via sort→group→unify with a representative; repeat until no new unifications occur. Only Id vars unify; effects are backtrackable.
- merge_group/4 (det, logical effects): For Key-[H|T], unify all Ids in T with H; Changed=true iff T is nonempty. Keys never unify.
- make_index/2 (det, pure): Build rbtree Id->[Keys] from canonical Nodes (Ids are the map keys). Rebuild after any Id aliasing.
- rules//3, rule//3 (nondet, pure): Apply each DCG rule Rule(Node,Index)// to Node. Rules may emit only Key-Id and (=)/2 items; must not inspect or bind Ids.
- match/4 (det, pure): Run Rules over the worklist using Index; collect concrete outputs (nodes and (=)/2). Output order: worklist order, then per-node rule order.
- push_back//1 (det, pure): O(1) append to DCG output via difference lists (scheduling only).
- rebuild//1 (det, logical effects): Apply (=)/2 equalities (alias Ids), enqueue new nodes, then canonicalize with merge_nodes//0. Only Id variables unify.
- unif/1 (semidet, impure by design): True for Eq=(A=B); performs A=B. Used only via exclude/3 in rebuild//1. Safe without occurs-check (Ids are fresh).
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4 (nondet, pure): Example rules/helpers. Emit only nodes/equalities; avoid in-place rewrites; restrict search via Index where applicable.
- extract/2, extract_node/1 (semidet, aliases Ids): Validation helpers for extract//0. Intentionally alias Ids via member/2; use only for validation and discard bindings.
- DCG bridging: Each DCG nonterminal compiles to a predicate with extra state args; merge_nodes//0 reuses merge_nodes/2 (called as merge_nodes(S0,S)).

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
%  Look up Id for Key in a canonical ordset (from merge_nodes/2).
%  - Pairs: sorted, exactly one Key-Id per Key.
%  - Prunes by standard order; confirms identity with (==) to preserve variable identity.
%  - Binds only Id; no mutation; fails if Key is absent.
%  Precondition: Pairs is canonical.
%  Notes: Ids are fresh logic vars used as class ids; never compare by name.
%  Complexity: O(N) worst case; prunes via compare/3 and early exits.
%  Determinism: semidet, steadfast, pure.
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
%  Insert Term and return its class Id; reuse Id if Key already exists.
%  - Compound: build Key=F(ChildIds) left-to-right (stable arg order ⇒ congruence).
%  - Atom/var: Key=Term; preserves variable identity (no variant/alpha-renaming).
%  - Pure producer: emits only Key-Id items; no Id unification; duplicates removed by merge_nodes/2.
%  Precondition (add/4): In is an ordset.
%  Notes: Ids are opaque logic variables (class ids). Canonicalize after any aliasing elsewhere.
%  Determinism: det; steadfast.
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
%  Ensure Node has a class Id; reuse if present, else insert Node-Id with a fresh Id.
%  - In/Out are ordsets; prune by standard order; confirm with (==) to preserve variable identity.
%  - No unification/canonicalization here; ord_add_element/3 preserves order and set semantics.
%  Precondition: In is an ordset.
%  Effect: fresh, unbound Id variable only when Node is new; Out=In if Node already exists.
%  Notes: Ids are logic variables (class ids); never compare by name.
%  Determinism: det; quasi-pure (no Id unification).
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
%  - IdA/IdB must be class Ids from this e-graph.
%  - Uses (=)/2 (no occurs-check); safe (Ids are fresh, acyclic vars).
%  Effect: Id aliasing only; Keys never unify; effects backtrackable.
%  Notes: Id aliasing may instantiate variables inside Keys; merge_nodes/2 collapses any new duplicates.
%  Determinism: det; logical effects (Id aliasing only).
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG wrapper for merge_nodes/2.
%  Determinism: det; steadfast.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize to one Key-Id per Key, repeating until stable.
%  - Algorithm: sort/2 → group_pairs_by_key/2 → unify each group’s Ids with the first.
%  - Repeats because unifying Ids can instantiate variables inside Keys and expose duplicates.
%  Complexity: O(N log N) per pass.
%  Effect: only Id variables unify; Keys never do.
%  Determinism: det; logical effects (Id unification only).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  For Key-[H|T], unify all Ids in T with H; report whether any unification occurred.
%  Effect: Keys never unify; only Id vars.
%  Notes: Unification may instantiate variables inside Keys; the next merge_nodes/2 pass collapses collisions.
%  Determinism: det; logical effects (Id unification).
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for +/2: from (A+B)-AB emit B+A-BA and AB=BA.
%  - Model equality without in-place rewrite; emit once per match.
%  Notes: BA is fresh; equality is consumed by rebuild//1. Rules must not inspect/bind Ids.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restrict to members of class(BC) via Index; emit at most one triple per match.
%  - If class(BC) is absent, emit nothing.
%  Notes: AB and ABC_ are fresh; unification deferred to rebuild//1. Rules must not inspect/bind Ids.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC) with A fixed.
%  - Emit at most one triple per qualifying member; confine rewrites to the class.
%  Notes: Pure producer; must not inspect/bind Ids.
%  Determinism: nondet over Members.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of +/2: if class(B) contains integer 0, emit A=AB.
%  - Use once/1 to avoid duplicates; match 0 exactly with (==).
%  Notes: Unification happens in rebuild//1; rules must not inspect/bind Ids.
%  Determinism: semidet.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums into a single constant.
%  - Introduce C for VC is VA+VB and emit VC-C, C=AB.
%  Notes: Uses is/2; preserves numeric type; pure producer. Unification deferred to rebuild//1.
%  Determinism: nondet; must not inspect/bind Ids.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Pick numeric VA in class(A), then search class(B) for numeric VB.
%  - Staged search avoids building pairs eagerly; guard with number/1.
%  Notes: Pure producer; unification deferred to rebuild//1.
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
%  For each numeric VB in class(B), compute VC is VA+VB and emit VC-C, C=AB.
%  Notes: number/1 guards are ensured by constant_folding_a//4. Pure producer; unification deferred to rebuild//1; must not inspect/bind Ids.
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
%  Apply each Rule(Node,Index)// to Node using Index; append outputs.
%  - Node is Key-Id; Rules may only emit Key-Id and (=)/2 items.
%  Notes: Pure producer; steadfast; must not inspect/bind Ids.
%  Determinism: nondet over Rules; each Rule runs once per Node (node order, then rule order).
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Call a single DCG rule Rule(Node,Index)// on Node.
%  Notes: Pure producer; must not inspect/bind Ids. Steadfast.
%  Determinism: as Rule//2.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build rbtree Index mapping Id -> [Keys] from canonical Nodes.
%  - Rebuild after any Id aliasing (Ids are the rbtree keys).
%  Notes: Ids are logic vars acting as class ids; the variable itself is the key. Never compare by name.
%  Complexity: O(N log N).
%  Determinism: det; pure; steadfast.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist using Index to produce Matches (nodes and (=)/2).
%  - Output order: worklist order, then per-node rule order.
%  Notes: Uses foldl/4 with rules//3; steadfast accumulator; does not inspect or bind Ids.
%  Determinism: det; produces a concrete list; no mutation or Id unification.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to the DCG output in O(1) via difference lists.
%  - Scheduling only; canonicalization is done by merge_nodes/2.
%  Notes: Idiomatic DCG trick (L, L --> []); steadfast; does not inspect or bind Ids.
%  Determinism: det; pure producer; no side effects.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (nodes and (=)/2), then canonicalize:
%    - exclude(unif, Matches, NewNodes): perform A=B; drop equalities.
%    - push_back(NewNodes): enqueue Key-Id items.
%    - merge_nodes: dedupe and unify Id classes.
%  Effect: only Id aliasing via (=)/2; backtrackable.
%  Notes: Id unification may instantiate variables in Keys; merge_nodes/2 repeats until stable. No other side effects.
%  Determinism: det; logical effects (Id unification only).
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Apply Rules to a length-based fixpoint (no new pairs/equalities).
%  Notes: Fixpoint uses node-list length; alias-only steps are invisible unless later rule outputs change size. Rules must be pure producers; must not inspect/bind Ids.
%  Determinism: det driver; rules must be pure producers.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run at most MaxSteps iterations (non-negative integer or inf).
%  - Fixpoint: compare lengths before/after rebuild (post merge_nodes/2).
%  - Alias-only steps do not change length; progress must add/remove pairs.
%  Notes: MaxSteps=inf is unbounded. Rules must not unify; only emit nodes/equalities; must not inspect/bind Ids.
%  Determinism: det driver; nondet arises only from Rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker that threads the e-graph explicitly.
%  - Rebuild Id->Keys index each iteration (Ids may alias).
%  - Stop when length is stable or MaxSteps exhausted; MaxSteps=inf is unbounded.
%  - Rules must be pure producers (emit nodes/equalities only). Unification happens only via rebuild//1.
%  Notes: Ids are mutable logic variables used as class ids; never compare by name. Always rebuild the index after aliasing.
%  Warning: MaxSteps=inf currently raises a type_error at (N > 0); treat inf specially in the guard or pass a large integer instead.
%  Determinism: det driver; nondet only from Rules.
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
%  - Intended only for rebuild//1 via exclude/3.
%  - Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic variables.
%  Notes: Only Id variables should appear here; Keys must not be unified. No occurs-check needed due to freshness/acyclicity.
%  Determinism: semidet; impure by design (Id unification).
unif(A=B) :- A=B.

%! extract(-Nodes) is semidet.
%  Validate and return Nodes.
%  Warning: aliases class Id variables via member/2; use for validation only.
%  To inspect without aliasing, use the node list directly.
%  Notes: Ids are logic variables; avoid using any bindings made here. Never compare Ids by name.
%  Determinism: semidet; aliases Ids.
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
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one Key; fails otherwise.
%  Warning: unifies each Id with one of its Keys via member/2 (validation only).
%  Notes: Intentionally aliases Ids; do not rely on any bindings produced.
%  Determinism: semidet; fails if any class is empty; aliases Ids.
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
