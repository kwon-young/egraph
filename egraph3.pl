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
- extract//0 uses member/2 and can alias Ids; prefer extract/1 in user code.

Public API
- add//2, union//2, saturate//1, saturate//2, extract/1, extract//0.

Implementation predicates (internal)
- lookup/2: O(N) read-only lookup in a canonical ordset of Key-Id. Prunes by standard order, then confirms with (==) to preserve variable identity. Pure; binds Val only; never touches Ids.
- add/4: worker for add//2. Builds Keys as F(ChildIds) (congruence) left-to-right and emits Node-Id pairs. Pure producer; no unification; duplicates allowed (merged later).
- add_node/4, add_node/3: ensure a Key has a class Id. Reuse existing Id or insert Node-Id with a fresh Id. Pure apart from allocating a fresh logic variable for the Id.
- merge_nodes//0, merge_nodes/2: canonicalize to one Key-Id per Key by sorting, grouping equal Keys, and unifying all Ids in each group into the first (representative). Iterate to a fixpoint because aliasing may expose new duplicates. Only unifies Id variables; effects are backtrackable.
- merge_group/4: unify all Ids in a group into the first; report whether any merge occurred. Det.
- make_index/2: build rbtree Id -> [Keys] from a canonicalized ordset. Requires merge_nodes/2 beforehand. Rebuild after any aliasing.
- rules//3, rule//3: run DCG rules over a Node with Index. Rules may only emit Key-Id items and (=)/2 equalities; no unification.
- match/4: collect rule outputs over the current worklist given Index. Pure; no mutation.
- push_back//1: append a list to the DCG output (difference-list scheduler) in O(1). Scheduling only; no deduplication.
- rebuild//1: apply (=)/2 equalities (alias Ids), enqueue new items, then canonicalize. The only place where Id variables are unified. Effects are logical/backtrackable.
- unif/1: recognize and execute (=)/2 on class Ids (used only via exclude/3 in rebuild//1). Deliberately impure; never call from user rules.
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4: internal example rules/helpers. Pure producers; never unify Ids directly.
- extract/2, extract_node/1: validation helpers used by extract//0. May alias Ids via member/2; use only for validation and discard any bindings.

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

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Read-only lookup in a canonical ordset of Key-Id pairs.
%  - Complexity: O(N).
%  - Key must be nonvar. Prunes by standard order, then confirms with (==) to preserve variable identity.
%  - Pure: binds Val only; never touches Key or Pairs. Fails if Key is absent.
%  - Pairs must be a strictly ordered ordset (from merge_nodes/2 or sort/2).
%  Notes: Ids are fresh logic variables (class Ids); do not unify/inspect them here. At most one match.
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
%  Insert Term and return its class Id; reuse the Id if Key already exists.
%  - Compound: Key = F(ChildIds), building ChildIds left-to-right (congruence).
%  - Atom/var: Key = Term (preserves variable identity; no variant-normalization).
%  - Pure producer: no unification/canonicalization; duplicates may appear (merged later).
%  - DCG variant threads a difference list; add/4 is the worker (uses foldl/5 to collect ChildIds).
%  Effects: allocates a fresh Id only when Key is new. Aliasing Ids elsewhere may instantiate variables inside Keys; run merge_nodes/2 afterwards.
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
%  Ensure Key Node has a class Id; reuse if present, else insert Node-Id with a fresh Id.
%  - In/Out are ordsets of Key-Id; prune by standard order, then confirm equality with (==).
%  - No unification/canonicalization here; run merge_nodes/2 after any Id aliasing elsewhere.
%  Effects: allocates a fresh Id only when Node is new; pure w.r.t. Keys.
%  Notes: ord_add_element/3 requires In to be an ordset. Ids are logic variables; never compare by print-name.
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
%  - IdA/IdB must be class Ids produced by this e-graph.
%  - Uses (=)/2 intentionally (no occurs-check); safe because Ids are fresh, acyclic logic variables.
%  Effects: only class-Id aliasing (logical/backtrackable). Keys are never unified.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG wrapper for merge_nodes/2.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize to one Key-Id per Key and return a sorted ordset.
%  - Steps: sort/2 -> group by Key -> unify all Ids in each group into the first (representative).
%  - Iterate to a fixpoint because aliasing can instantiate variables inside Keys and expose new duplicates.
%  - Complexity: O(N log N) per pass; extra passes only when aliasing exposes new merges.
%  Effects: unifies Id variables only; Keys are never unified. Equality preserves variable identity via (==) after ordering.
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Unify all Ids in a group into the first; Changed=true iff the group had >1 Id.
%  - Rep is the first Id; each tail Id is unified with Rep.
%  - Changed feeds merge_nodes/2's outer fixpoint.
%  Note: Unifying Ids may instantiate variables inside Keys; a subsequent pass may then reveal duplicates.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for +(A,B): from (A+B)-AB emit B+A-BA and AB=BA.
%  - Models equality without in-place rewrites; both orders share the class.
%  - Matches only +(A,B) nodes; emits exactly one result per match (avoids blow-up).
%  Note: BA is a fresh Id; AB=BA is later consumed by rebuild//1.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restricts candidates to members of class(BC) using Index (avoids quadratic search).
%  Note: AB and ABC_ are fresh Ids; ABC=ABC_ is later consumed by rebuild//1.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC), keeping A fixed.
%  - Members is the list of Keys in class(BC) (from Index).
%  - Confines rewrites to the current equivalence class; emits nodes/equalities only.
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
%  Notes: Uses (==) to match 0 exactly (not 0.0). Emits A=AB; unification happens in rebuild//1.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums (integers/floats) into a single constant.
%  - Shrinks the search space by canonicalizing ground arithmetic; introduces C and preserves AB via C=AB.
%  Notes: Evaluation uses is/2. Emits nodes/equalities only; unification is deferred to rebuild//1.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Helper: pick numeric VA in class(A), then search class(B) for numeric VB.
%  Staged search avoids building pairs eagerly.
%  - Emits nodes/equalities only; unification happens in rebuild//1.
%  Determinism: nondet over numeric members of class(A) and class(B); emits one pair per numeric combination.
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
%  - Introduces fresh C for VC while preserving AB as the class Id for the sum via C=AB.
%  Notes: Arithmetic uses is/2. Emits nodes/equalities only; unification is deferred to rebuild//1.
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
%  Apply each DCG Rule(Node,Index)// to Node, given Index; nondet over Rules.
%  - Rules may only emit Key-Id items and (=)/2 equalities; no unification.
%  - Appends outputs to the DCG stream; rebuild//1 later consumes them.
%  - Uses sequence/2 (library(dcg/high_order)) to iterate rules in order.
%  Determinism: nondet over Rules; each Rule is called exactly once per Node (node order, then rule order).
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule Rule(Node,Index)// on Node.
%  - Rule is a DCG nonterminal Rule//2 (compiles to Rule/4).
%  - Rule must not perform unification; only emit nodes and (=)/2 items.
%  Determinism: matches the determinism of Rule//2.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree Index mapping Id -> [Keys] from a canonicalized ordset of Key-Id.
%  - Complexity: O(N log N).
%  - Requires Nodes canonicalized by merge_nodes/2 (sorted and deduped by Key).
%  - Ids may alias; rebuild after any aliasing (rebuild//1 or merge_nodes/2).
%  Note: uses transpose_pairs/2 and group_pairs_by_key/2.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce Matches (Key-Id items and (=)/2 equalities).
%  - Worklist is the current node set (ordset of Key-Id pairs).
%  - Rules must not perform unification; only emit nodes and equalities.
%  - Matches are consumed by rebuild//1 (the only place Id variables are unified).
%  - Output order: Worklist order, then per-node rule order.
%  Determinism: det; produces a list; no mutation.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to the end of the DCG output in O(1) via difference lists.
%  - Scheduling only; no deduplication and no unification.
%  - Use with ordset-like streams; canonicalization happens in merge_nodes/2.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (Key-Id items and (=)/2 equalities) and canonicalize:
%    - exclude(unif, Matches, NewNodes): perform A=B unifications; drop equalities.
%    - push_back(NewNodes): enqueue remaining Key-Id items.
%    - merge_nodes: canonicalize the graph.
%  Effects: only class-Id aliasing via (=)/2 (logical/backtrackable). Equalities are consumed; deduplication happens in merge_nodes/2.
%  Notes: unif/1 is the sole place where (=)/2 is executed; use only via exclude/3 here. Id aliasing may instantiate variables inside Keys.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Apply Rules until a fixpoint (no new Key-Id items/equalities). See caveat on alias-only steps.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run at most MaxSteps iterations (non-negative integer or inf).
%  - Fixpoint test: compare lengths before/after rebuild (after merge_nodes/2).
%  - Alias-only steps do not change length; rules must eventually add/remove pairs to be observed.
%  Determinism: det driver; nondet arises only from Rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker that threads the e-graph explicitly.
%  - Rebuilds the Id->Keys index each iteration because Id variables may alias.
%  - Fixpoint is length-based; alias-only progress is invisible to the stop test.
%  - Rules must be pure producers (emit nodes/equalities only). Unification happens via rebuild//1.
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
%  True for Eq=(A=B); performs the unification as a side effect.
%  - Use with exclude/3 to apply equalities and drop them from a worklist.
%  Effects: intentionally unifies class Id variables; fails for non-(=)/2 items. Effects are logical/backtrackable.
%  Notes: Deliberately impure and used only by rebuild//1. Uses (=)/2 (no occurs-check); safe because Ids are fresh, acyclic logic variables. Never call from user rules.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Return the current nodes (no validation).
%  Prefer in user code to avoid Id aliasing during validation.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  Validate: every Id-class has at least one concrete Key.
%  Warning: uses member/2 and can alias/bind Ids; use only for validation or under backtracking. Prefer extract/1 in user code.
%! extract(+Nodes, -Nodes) is semidet.
%  Helper for extract//0; succeeds iff each Id-group has a concrete Key.
%  Note: typically called with the same variable to avoid copying; may alias Ids — discard any bindings afterwards.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one concrete Key; fails otherwise.
%  Minimal consistency check; may bind/alias Ids via member/2 (validation only).
%  Note: Uses member/2 on Keys and thus can alias Id variables; use only for validation and discard any aliases.
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
