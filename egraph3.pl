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
- lookup/2: O(N) read-only lookup in a canonical ordset of Key-Id; first prunes by standard order, then confirms with (==) to preserve variable identity. Pure; binds only the value.
- add/4: worker behind add//2; builds Keys as F(ChildIds) (congruence) left-to-right and appends Node-Id pairs. Pure producer; no unification; may introduce duplicates.
- add_node/4, add_node/3: ensure a Key has a class Id; reuse existing Id or insert Node-Id with a fresh Id. Pure except for allocating a fresh logic var.
- merge_nodes//0, merge_nodes/2: canonicalize to one Key-Id per Key by sorting, grouping equal Keys, and unifying all Ids in each group into the first; iterate to a fixpoint after aliasing. Only unifies Id variables; backtrackable.
- merge_group/4: unify all Ids in a Key-group into the first (representative); report whether any merge occurred. Deterministic.
- make_index/2: build rbtree Id -> [Keys] from a canonicalized ordset. Assumes prior merge_nodes/2; Index must be rebuilt after any aliasing.
- rules//3, rule//3: run DCG rules over a node with Index; rules must only emit Key-Id items and A=B equalities. No unification here.
- match/4: collect rule outputs over the current worklist given Index. Pure; no mutation.
- push_back//1: append a list to the DCG output (difference-list scheduler) in O(1). Scheduling only; no deduplication.
- rebuild//1: apply (=)/2 equalities (alias Ids), enqueue new items, then canonicalize; the only place where unification of Ids happens. Effects are logical/backtrackable.
- unif/1: recognize and execute (=)/2 on class Ids (used only via exclude/3 in rebuild//1). Impure by design; never call from user rules.
- comm//2, assoc//2, assoc_//3, reduce//2, constant_folding//2, constant_folding_a//4, constant_folding_b//4: internal example rules/helpers; pure producers that never unify Ids directly.
- extract/2, extract_node/1: validation helpers used by extract//0; may alias Ids via member/2, so use only for validation and discard any bindings.

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
%  Read-only O(N) lookup in a canonical ordset of Key-Id pairs.
%  - Key must be nonvar. Prune via standard order, then confirm with (==) to preserve variable identity.
%  - Binds Val only; Pairs is not modified. Fails if Key is absent.
%  Notes:
%    - Ids are opaque class identifiers (fresh logic variables). Do not unify or inspect them here.
%    - Pairs must be a strictly ordered ordset.
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
%  Insert Term and return its class Id; reuse an existing Id if the Key already exists.
%  - Compound: Key = F(ChildIds) built left-to-right (congruence).
%  - Atomic/var: Key = Term (variable identity preserved; no alpha/variant normalization).
%  - Pure producer: no canonicalization/unification; duplicates may appear. Run merge_nodes/2 after any aliasing.
%  - DCG form threads nodes via difference lists; add/4 is the worker.
%  Effects: allocate fresh Ids only; Keys are never unified here.
%  Notes:
%    - Id is a fresh logic variable (mutable class Id). Aliasing Ids may instantiate variables embedded in Keys; effects are logical and backtrackable.
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
%  - In/Out are ordsets of Key-Id; equality prunes by order then confirms with (==) to preserve variable identity.
%  - No unification/canonicalization; run merge_nodes/2 after any Id aliasing.
%  Effects: only allocates a fresh Id when Node is new.
%  Notes: ord_add_element/3 assumes In is an ordset; callers must preserve this invariant.
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
%  - Unifying Ids may instantiate variables inside Keys; rules can rely on this.
%  - Uses (=)/2 intentionally (no occurs-check); safe because Ids are fresh, acyclic logic variables.
%  Effects: Id aliasing only (backtrackable).
%  Determinism: det.
%  Note: Always follow with merge_nodes/2 to collapse duplicates created by aliasing.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG alias that threads the state through merge_nodes/2.
%! merge_nodes(+In, -Out) is det.
%  Canonicalize to one Key-Id per Key: sort, group equal Keys, unify all Ids in each group into the first; iterate to a fixpoint.
%  - Complexity: O(N log N) per pass; extra passes if Id unification instantiates vars inside Keys.
%  - Effects: only Id unification; Keys are never unified.
%  Notes:
%    - Key equality preserves variable identity via (==) after ordering.
%    - Repeat while any group has >1 Id or resorting after aliasing exposes new duplicates.
%    - Terminates: each pass either aliases ≥1 pair of Ids or leaves the set unchanged.
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Unify all Ids in a Key-group into the first; set Changed=true iff the group has >1 Id.
%  - Rep is the first Id; unify each tail Id with Rep.
%  - Changed threads into the outer fixpoint in merge_nodes/2.
%  Notes: Id unification may instantiate variables inside Keys; resorting may expose new duplicates.
%  Determinism: det.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for +(A,B): from (A+B)-AB emit B+A-BA and AB=BA.
%  Models equality without in-place rewrites; both orders share the class.
%  Matches only +(A,B) nodes; emits at most one result per match.
%  Note: BA is a fresh Id for B+A; AB=BA is consumed by rebuild//1 to alias classes.
%  Determinism: nondet over the worklist; at most one emission per matching node (prevents duplicate blow-up).
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  Restrict candidates to members of class(BC) via Index to avoid quadratic search over unrelated nodes.
%  Note: AB and ABC_ are fresh Ids; ABC=ABC_ is consumed by rebuild//1 to alias. The rule only emits nodes/equalities.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC), keeping A fixed.
%  - Members is the list of Keys in class(BC) (from Index).
%  - Confines candidate rewrites to the current equivalence class.
%  - Emits nodes/equalities only; unification happens later in rebuild//1.
%  Determinism: nondet over Members.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of +/2: if class(B) contains the integer 0, emit A=AB.
%  Eliminates the unit; once/1 avoids duplicates.
%  Notes:
%    - Use (==) to match 0 exactly (not 0.0); only Keys already bound to 0 qualify.
%    - Emit A=AB; unification happens later in rebuild//1 (the rule itself does not unify).
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums (integers/floats) into a single constant.
%  Shrinks the search space by canonicalizing ground arithmetic; introduces fresh C and preserves AB via C=AB.
%  Notes:
%    - Evaluation uses is/2.
%    - Emits nodes/equalities only; no unification here (rebuild//1 consumes (=)/2).
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Helper: pick numeric VA in class(A); then search class(B) for numeric VB.
%  Staged search avoids building pairs eagerly.
%  - Emits nodes/equalities only; unification happens in rebuild//1.
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
%  Helper: for each numeric VB in class(B) compute VC is VA+VB; emit VC-C and C=AB.
%  Introduces fresh C for VC while preserving AB as the class Id for the sum via C=AB (consumed by rebuild//1).
%  Notes:
%    - Arithmetic uses is/2; evaluation follows Prolog's numeric tower and type promotion rules.
%    - Emits nodes/equalities only; unification is deferred to rebuild//1.
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
%  Apply each DCG Rule(Node,Index)// to Node, given Index; nondet over Rules.
%  - Purity: rules may only emit Key-Id items and (=)/2 equalities; no unification.
%  - Scheduling: append outputs to the DCG stream; rebuild//1 later consumes them.
%  - Uses sequence/2 from library(dcg/high_order) to iterate rules.
%  - Ids are mutable logic variables; rules must not unify them directly.
%  Determinism: nondet over Rules; each Rule is called exactly once per Node.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule Rule(Node,Index)// on Node.
%  - Rule must be a DCG nonterminal Rule//2; it compiles to Rule/4: Rule(+Node,+Index,?Out,?Tail).
%  - Rule must not perform unification; only emit nodes and (=)/2 items.
%  Determinism: matches the determinism of Rule//2 (wrapper adds no extra choice points).
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree Index mapping Id -> [Keys] from a canonicalized ordset of Key-Id pairs.
%  - Complexity: O(N log N) (grouping + tree build).
%  - Ids are logic variables and may alias; always rebuild after aliasing.
%  - Assumes Nodes were canonicalized by merge_nodes/2.
%  - Index is ephemeral/read-only; rebuild or discard after each aliasing step.
%  Notes: uses transpose_pairs/2 and group_pairs_by_key/2 (autoload from library(pairs)).
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce Matches (Key-Id items and (=)/2 equalities).
%  Central collection step before rebuild. Worklist is the current node set (ordset of Key-Id pairs).
%  - Rules must not perform unification; only emit nodes and equalities.
%  - Matches are consumed by rebuild//1 (the only place where Id variables are unified).
%  - Ids are opaque logic variables; update them only via (=)/2 in rebuild//1.
%  Determinism: det given Rules/Worklist/Index; produces a (possibly empty) list; no mutation.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  Append List to the end of the DCG output in O(1) via difference lists.
%  Schedules newly discovered items after the current worklist.
%  - Purely structural; no deduplication and no unification side effects.
%  - Defined as `push_back(L), L --> []` (difference-list DCG; zero-copy).
%  - Use with ordset-like streams; canonicalization happens in merge_nodes/2.
%  Determinism: det.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply Matches (Key-Id items and (=)/2 equalities) and canonicalize:
%    - exclude(unif, Matches, NewNodes): perform A=B unifications; drop equalities.
%    - push_back(NewNodes): schedule remaining Key-Id items.
%    - merge_nodes: canonicalize the graph.
%  Effects: only class-Id aliasing via (=)/2 (logical, backtrackable). Equalities are consumed; no other mutation. Deduplication occurs only in merge_nodes/2.
%  Notes:
%    - unif/1 intentionally performs side-effect unification of Id variables; use only via exclude/3 here. This is the sole place where (=)/2 is executed.
%    - Uses library(apply): exclude/3 (autoload).
%    - Unifying Ids may instantiate variables inside Keys; merge_nodes/2 then collapses duplicates.
%  Determinism: det.
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
%  - Fixpoint test: compare lengths before/after rebuild (post-merge_nodes/2).
%  - Alias-only steps do not change length; rules must eventually add/remove pairs.
%  Determinism: det driver; nondet arises only from Rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker: thread the e-graph explicitly.
%  - MaxSteps: non-negative integer or inf.
%  - Each iteration rebuilds the Id->Keys index because Id variables may alias.
%  - Fixpoint is length-based; alias-only progress is invisible.
%  - Rules must be pure producers (emit nodes/equalities only). Any unification they rely on must happen via rebuild//1.
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
%  Use with exclude/3 to apply equalities and drop them from a worklist.
%  Effects: intentionally unifies class Id variables; fails for non-(=)/2 items. Effects are logical and backtrackable.
%  Notes:
%    - Deliberately impure; used only by rebuild//1.
%    - Non-(=)/2 items fail here and are retained by exclude/3.
%    - Uses (=)/2 (no occurs-check); safe because only fresh, acyclic Id variables are unified.
%    - Never call directly from user rules; keep unification centralized in rebuild//1.
%  Determinism: semidet; succeeds once on (=)/2, fails otherwise.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Return the current nodes (no validation).
%  Prefer this in user code to avoid Id aliasing during validation.
%  Determinism: det.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  Validate: every Id-class has at least one concrete Key.
%  Warning: uses member/2 and can alias/bind Ids; use only for validation or under backtracking. Prefer extract/1 in user code.
%! extract(+Nodes, -Nodes) is semidet.
%  Helper for extract//0; succeeds iff each Id-group has a concrete Key.
%  Note: typically called with the same variable to avoid copying; do not rely on side effects (may alias Ids).
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one concrete Key; fails otherwise.
%  Minimal consistency check; may bind/alias Ids via member/2 (validation only).
%  Note: uses member/2 on Keys and thus can alias Id variables; use only for validation and discard any aliases.
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
