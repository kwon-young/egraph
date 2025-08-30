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
- lookup/2 (semidet, pure, steadfast): Read-only Id lookup in a canonical ordset. Prunes by standard order, then confirms Key with (==) to preserve variable identity. Binds Id only; never touches Ids.
- add/4 (det, pure w.r.t. Keys): Worker for add//2. Builds Key=F(ChildIds) left-to-right (congruence; stable arg order). Emits only Key-Id pairs; duplicates are removed by merge_nodes/2.
- add_node/4, add_node/3 (det, quasi-pure): Ensure a Key has a class Id. Reuse if present; otherwise insert Key-Id with a fresh logic variable. No canonicalization or unification here.
- merge_nodes//0, merge_nodes/2 (det, logical effects): Canonicalize to one Key-Id per Key via sort→group→unify group Ids with a representative. Iterate to a fixpoint because Id aliasing can instantiate variables in Keys and reveal new duplicates. Only Id variables unify; effects are backtrackable.
- merge_group/4 (det, logical effects): Unify all Ids in a group with the head Id; Changed=true iff the group has more than one Id.
- make_index/2 (det, pure): Build rbtree Id->[Keys] from a canonical ordset. Rebuild after any Id aliasing (the Id variable itself is the map key).
- rules//3, rule//3 (nondet, pure): Apply DCG rules to a Node with Index. Rules may only emit Key-Id items and (=)/2 equalities; never unify Ids directly.
- match/4 (det, pure): Collect rule outputs over Worklist with Index into a concrete list. No mutation or Id unification.
- push_back//1 (det, pure): O(1) append to the DCG output (difference lists). Scheduling only; no deduplication; canonicalization happens in merge_nodes/2.
- rebuild//1 (det, logical effects): Apply (=)/2 equalities (alias Ids), enqueue items, then canonicalize via merge_nodes//0. This is the only place class Id variables unify.
- unif/1 (semidet, impure by design): True for Eq=(A=B); performs the unification. Used only via exclude/3 inside rebuild//1; not for user rules.
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4 (nondet, pure): Example rules/helpers. Emit only nodes and equalities; no direct unification (rebuild//1 handles aliasing).
- extract/2, extract_node/1 (semidet, aliases Ids): Validation helpers for extract//0. Intentionally alias Ids via member/2; use only for validation and discard any bindings.
- DCG bridging: DCG nonterminals are implemented by same-name predicates with DCG state arguments; in particular, merge_nodes//0 is provided by merge_nodes/2 and is called as merge_nodes(S0,S) after DCG expansion.

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
%  Read-only lookup of Id for Key in canonical ordset Pairs.
%  - Pairs must be a strictly ordered ordset as from merge_nodes/2.
%  - Prunes by standard order, then confirms Key identity with (==) to preserve variable identity (no variant normalization).
%  - Only binds Id; never mutates Keys or stored Ids; fails if Key is absent.
%  - Ids are fresh logic variables used as mutable class identifiers; never compare by print-name.
%  Determinism: semidet; steadfast; pure.
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
%  - Compound: Key = F(ChildIds) built left-to-right (stable arg order; enforces congruence).
%  - Atom/var: Key = Term; preserves variable identity (no alpha/variant normalization).
%  - Pure producer: only emits Key-Id; no unification. Duplicates are removed later by merge_nodes/2.
%  - add//2 is the DCG front; add/4 is the worker; foldl/4 builds ChildIds.
%  Effect: allocates a fresh Id only for new Keys. Id aliasing may instantiate vars in Keys; always follow aliasing with merge_nodes/2.
%  Determinism: det; pure w.r.t. Keys.
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
%  - In/Out are ordsets; prune by standard order and confirm identity with (==) to preserve variable identity.
%  - No unification and no canonicalization here; call merge_nodes/2 after any Id aliasing elsewhere.
%  Effect: fresh Id only when Node is new; Out=In if Node already exists. Pure w.r.t. Keys.
%  Notes:
%  - In must be an ordset; ord_add_element/3 preserves order and set semantics.
%  - Ids are logic variables used as mutable class identifiers; never compare by print-name.
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
%  Alias two classes by unifying IdA with IdB, then canonicalize with merge_nodes/2.
%  - IdA and IdB must be class Ids from this e-graph.
%  - Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic logic variables.
%  Effect: only Id aliasing (logical/backtrackable). Keys never unify here.
%  Note: merge_nodes/2 is required because aliasing may instantiate variables inside Keys and reveal duplicate Keys.
%  Determinism: det; logical effects (Id aliasing only).
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG wrapper for merge_nodes/2; expands to merge_nodes(S0,S).
%  Determinism: det.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize to one Key-Id per Key; return a sorted ordset.
%  - Algorithm: sort/2 → group_pairs_by_key/2 → unify each group’s Ids with the first (representative).
%  - Uses foldl/5 with merge_group/4 to map groups and OR-accumulate a Changed flag.
%  - Repeat until stable because unifying Ids may instantiate variables inside Keys and expose new duplicates.
%  - Complexity: O(N log N) per pass.
%  Effect: only Id variables unify; Keys never do. Key equality uses standard order, then (==) to preserve variable identity.
%  Notes:
%  - Recurse only if any group has >1 Id (Changed=true).
%  - Ids are logic variables used as mutable class identifiers; never compare by print-name.
%  Determinism: det; logical effects (Id unification only).
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Map a group to Key-Rep and report whether any unification occurred.
%  - Rep is the first Id; unify each tail Id with Rep; Changed=true iff the group has >1 Id.
%  - Used by foldl/5 in merge_nodes/2 to map groups and OR-accumulate Changed.
%  Notes:
%  - Unifying Ids can instantiate variables inside Keys; later passes may expose duplicates.
%  Determinism: det; logical effects (Id unification only).
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for +/2: from (A+B)-AB emit B+A-BA and AB=BA.
%  - Models equality without in-place rewrites; both orders share the class.
%  - Match only +(A,B); emit exactly one result per match (avoid blow‑up).
%  Note: BA is fresh; AB=BA is consumed by rebuild//1 (the only place Ids unify).
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restrict candidates to members of class(BC) via Index (avoid quadratic search).
%  Notes:
%  - AB and ABC_ are fresh.
%  - ABC=ABC_ is consumed by rebuild//1 (the only place Ids unify).
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC) with A fixed.
%  - Members is the list of Keys in class(BC) (from Index).
%  - Confine rewrites to the current class; emit nodes/equalities only.
%  - AB and ABC_ are fresh; equalities are deferred to rebuild//1.
%  Determinism: nondet over Members; at most one triple per qualifying member.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of +/2: if class(B) contains the integer 0, emit A=AB.
%  - Eliminates the unit; once/1 avoids duplicates.
%  Note: Use (==) to match 0 exactly (not 0.0). Unification happens in rebuild//1.
%  Determinism: semidet.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums (integers/floats) into a single constant.
%  - Shrinks the search space by canonicalizing ground arithmetic; introduce C and preserve AB via C=AB.
%  Notes:
%  - Uses is/2 for evaluation and preserves the numeric type.
%  - Emits nodes/equalities only; unification is deferred to rebuild//1.
%  Determinism: nondet.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Helper: pick numeric VA in class(A), then search class(B) for numeric VB.
%  - Staged search avoids building pairs eagerly.
%  - Emit nodes/equalities only; unification is deferred to rebuild//1.
%  - Guard with number/1 on both sides; VB is handled in constant_folding_b//4.
%  Determinism: nondet over numeric members of class(A) and class(B); one pair per numeric combination.
constant_folding_a([VA | ANodes], B, AB, Index) -->
   (  {number(VA)}
   -> {rb_lookup(B, BNodes, Index)},
      constant_folding_b(BNodes, VA, AB, Index)
   ;  []
   ),
   constant_folding_a(ANodes, B, AB, Index).
constant_folding_a([], _, _, _) --> [].
%! constant_folding_b(+ClassB, +VA, -AB, +Index)// is nondet.
%  Helper: for each numeric VB in class(B), compute VC is VA+VB; emit VC-C and C=AB.
%  - Introduce fresh C for VC while preserving AB as the class Id for the sum via C=AB.
%  Notes:
%  - Arithmetic uses is/2; guards in constant_folding_a//4 ensure both sides are numbers.
%  - Emits nodes/equalities only; unification is deferred to rebuild//1.
%  Determinism: nondet over numeric members of class(B); one emission per numeric VB.
constant_folding_b([VB | BNodes], VA, AB, Index) -->
   (  {number(VB)}
   -> {VC is VA + VB},
      [VC-C, C=AB]
   ;  []
   ),
   constant_folding_b(BNodes, VA, AB, Index).
constant_folding_b([], _, _, _) --> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply each Rule(Node,Index)// to Node using Index; nondet over Rules.
%  - Node is Key-Id; Id is an opaque class Id (logic variable).
%  - Rules is a list of DCG nonterminals Rule//2; they may only emit Key-Id items and (=)/2 equalities.
%  - Appends outputs to the DCG stream; rebuild//1 consumes them.
%  - Iteration uses sequence/2 (library(dcg/high_order)).
%  Determinism: nondet over Rules; each Rule runs once per Node (node order, then rule order).
%  Steadfast; pure producer (must not inspect or bind Ids).
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Call a single DCG rule Rule(Node,Index)// on Node.
%  - Node is Key-Id; Id is an opaque class Id (logic variable).
%  - Rule is a DCG nonterminal Rule//2 (compiles to Rule/4).
%  - Rule must not unify; only emit nodes and (=)/2 items.
%  Notes: Called by rules//3; keep pure and do not inspect or bind Ids.
%  Determinism: as Rule//2.
%  Steadfast; pure producer (must not inspect or bind Ids).
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build rbtree Index mapping Id -> [Keys] from a canonical ordset of Key-Id.
%  - Complexity: O(N log N).
%  - Precondition: Nodes must be canonicalized by merge_nodes/2 (sorted, deduped by Key).
%  - Ids may alias via unification; rebuild the index after any aliasing (rebuild//1 or merge_nodes/2).
%  Notes:
%  - Uses transpose_pairs/2 and group_pairs_by_key/2; the rbtree key is the Id logic variable itself (mutable by unification).
%  - Never compare Ids by print-name; the variable identity is the key.
%  Determinism: det; pure.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce Matches (Key-Id items and (=)/2 equalities).
%  - Worklist is the current node set (ordset of Key-Id pairs).
%  - Rules must not unify; only emit nodes and equalities.
%  - Matches are consumed by rebuild//1 (the only place Id variables unify).
%  - Output order: Worklist order, then per-node rule order.
%  Notes: Implemented via foldl/4 with rules//3; purely accumulative and steadfast.
%  Determinism: det; produces a concrete list; no mutation or Id unification here.
%  Steadfast; pure accumulator; does not inspect or bind Ids.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to the end of the DCG output in O(1) via difference lists.
%  - Scheduling only; no deduplication and no unification.
%  - Use with ordset-like streams; canonicalization happens in merge_nodes/2.
%  Notes: Idiomatic DCG trick (L, L --> []); steadfast; does not inspect or bind Ids.
%  Determinism: det; pure producer.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (Key-Id items and (=)/2 equalities), then canonicalize:
%    - exclude(unif, Matches, NewNodes): apply A=B unifications; drop equalities.
%    - push_back(NewNodes): enqueue remaining Key-Id items.
%    - merge_nodes: canonicalize the graph (dedupe and unify Ids per group).
%  Effect: only Id aliasing via (=)/2 (logical/backtrackable). Equalities are consumed; deduplication happens in merge_nodes/2.
%  Notes:
%  - The only place where (=)/2 is executed (via unif/1 and exclude/3), and thus the only place where Id variables unify.
%  - Unifying Ids may instantiate variables inside Keys; always follow with merge_nodes/2.
%  Determinism: det; logical effects (Id unification only).
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Apply Rules to a length-based fixpoint (no new pairs/equalities observed). See caveat on alias-only steps.
%  Notes: Fixpoint is based on node-list length; alias-only steps are invisible unless later rule outputs change size.
%  Determinism: det driver.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run at most MaxSteps iterations (non-negative integer or inf).
%  - Fixpoint test: compare lengths before/after rebuild (after merge_nodes/2).
%  - Alias-only steps do not change length; rules must eventually add/remove pairs to be observed.
%  Notes: MaxSteps=inf means unbounded.
%  Determinism: det driver; nondet arises only from Rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker that threads the e-graph explicitly.
%  - Rebuild Id->Keys index each iteration because Id variables may alias.
%  - Fixpoint is length-based; alias-only progress is invisible to the stop test.
%  - Rules must be pure producers (emit nodes/equalities only). Unification happens via rebuild//1.
%  Notes:
%  - MaxSteps=inf means "no bound". Use a small bound to debug rule sets; increase if convergence is slow.
%  - Ids are logic variables acting as mutable class identifiers; always rebuild the index after aliasing.
%  Determinism: det driver; nondet comes only from Rules.
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
%  - Use with exclude/3 to apply equalities and drop them from a worklist.
%  Effect: intentionally unifies class Id variables; fails for non-(=)/2 items. Effects are logical/backtrackable.
%  Notes:
%  - Deliberately impure and used only by rebuild//1. Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic logic variables.
%  - Never call from user rules; this is a rebuild helper.
%  - Ids are logic variables acting as mutable unique identifiers (by aliasing).
%  Determinism: semidet; impure by design (Id unification).
unif(A=B) :- A=B.

%! extract(-Nodes) is semidet.
%  Validate and return Nodes.
%  Warning: aliases class Id variables via member/2 (through extract/2); use for validation only.
%  To inspect without aliasing, use the node list directly (do not call extract/*).
%  Determinism: semidet; aliases Ids.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  Validate: every Id-class has at least one Key witness.
%  Warning: intentionally uses member/2 to instantiate each Id to one of its Keys; use only for validation/backtracking. Prefer extract/1 in user code.
%! extract(+Nodes, -Nodes) is semidet.
%  Helper for extract//0; succeeds iff each Id-group is nonempty.
%  Notes: Typically called with the same variable to avoid copying; aliases Ids — discard any bindings afterwards.
%  Determinism: semidet; aliases Ids; pure w.r.t. Keys.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one Key; fails otherwise.
%  Minimal consistency check; unifies each Id with some Key via member/2 (validation only).
%  Notes: This aliases/binds Id variables; use only for validation and discard any aliases afterwards. Ids are mutable via unification.
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
