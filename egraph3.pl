:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs with congruence closure for Prolog terms.

Core model
- Nodes: ordset of Key-Id pairs (standard order). A Key is an atom/var or a term F(ChildIds). Variable identity is part of the Key (no alpha/variant normalization).
- Class Ids: fresh logic variables act as mutable, backtrackable class identifiers. The only mutation is aliasing classes by unifying Id variables with (=)/2.
- Canonicalization: merge_nodes/2 collapses duplicates so there is at most one Key-Id per Key; after each canonicalization, an Id→Keys index is rebuilt.

Execution
- DCGs thread the node set as a difference list. Rules only emit Key-Id items and equalities A=B; they never unify themselves.
- rebuild//1 consumes equalities (unifies Ids), appends new items to the worklist, and calls merge_nodes/2.
- Unifying Ids may instantiate variables inside Keys; merge_nodes/2 iterates until no further merges appear.

Caveats
- Fixpoint in saturate//2 is length-based; alias-only steps (A=B with no new pairs) are invisible to the stop condition.
- Never serialize or compare Ids by print-name; treat them as opaque logic variables.
- extract//0 uses member/2 and can alias Ids; prefer extract/1 in user code.

Public API
- add//2, union//2, saturate//1, saturate//2, extract/1, extract//0.

Implementation predicates (internal)
- merge_nodes/2: canonicalize to one Key-Id per Key; repeat to a fixpoint.
- make_index/2: rbtree index Id -> [Keys] from a canonicalized ordset.
- rebuild//1: apply equalities, schedule new nodes, then canonicalize.

Equality and identity
- Key equality is determined after standard ordering and confirmed with (==), preserving variable identity.
- All effects are logical and backtrackable. Only Id variables unify; no occurs-check is needed because Ids are fresh, acyclic logic variables.

Notes
- Using logic variables as class Ids is intentional: unification is the only mutating operation and is backtrackable. This can instantiate variables embedded inside Keys; always follow Id aliasing with merge_nodes/2.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Read-only lookup in an ordset of Key-Val pairs (standard order).
%  - Requires: Pairs is a strictly ordered ordset; Key must be nonvar.
%  - Equality: narrow by standard order, then confirm with (==) so variable identity in Keys is preserved.
%  - Complexity: O(N) scan (small unrolled window). Pure (does not bind Keys); unifies Val on success; fails if absent.
%  Note: intentional O(N) for simplicity/locality over asymptotics.
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
%  - Compound: add subterms left-to-right; Key = F(ChildIds) (congruence).
%  - Atomic/var: Key = Term. Variable identity is part of the Key (no alpha/variant-normalization).
%  - No canonicalization here; duplicates may be introduced. Use merge_nodes/2 to collapse.
%  Notes:
%    - Id is a fresh logic variable (mutable class Id via unification). Unifying Ids may instantiate variables inside Keys; effects are logical and backtrackable.
%    - DCG state is an ordset of Key-Id pairs (standard order). Rules do not unify; equalities are consumed by rebuild//1.
%    - Pure w.r.t. Keys: only creates fresh Id variables; no other bindings.
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
%  Ensure Node has a class Id; reuse existing Id if present, else insert Node-Id.
%  - In/Out are ordsets of Key-Id (standard order). Equality after ordering uses (==).
%  - No unification or canonicalization here; call merge_nodes/2 after any aliasing.
%  Side-effects: none (except allocating a fresh Id when Node is new). Determinism: det.
%  Notes:
%    - Ids are logic variables serving as mutable, unique class Ids (by later unification).
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%! union(+IdA, +IdB, +In, -Out) is det.
%  Alias classes by unifying IdA with IdB, then canonicalize with merge_nodes/2.
%  - IdA/IdB must be class Ids from this graph.
%  - Unifying Ids may instantiate variables inside Keys; many rules rely on this.
%  - Uses (=)/2 (no occurs-check); safe because only Id variables are unified.
%  Side-effects: only Id aliasing (backtrackable). Determinism: det.
%  Notes:
%    - Always follow with merge_nodes/2 to collapse duplicate Keys created by aliasing.
%    - Equality is applied logically and is fully backtrackable.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG alias of merge_nodes/2 (expands to merge_nodes(+In,-Out)).
%! merge_nodes(+In, -Out) is det.
%  Canonicalize: sort by Key, group equal Keys, unify Ids within each group into the first; repeat to a fixpoint.
%  - Complexity: O(N log N) per pass (sort+group); multiple passes if unification instantiates vars inside Keys.
%  - Effects: only Id unifications; Keys are never unified. Determinism: det.
%  Notes:
%    - Exactly one Key-Id per Key at fixpoint; preserves variable identity in Keys.
%    - Another pass runs if any group had >1 Id or resorting reveals new duplicates.
%    - Ids are logic variables; unification can ground/instantiate variables embedded in Keys, enabling new merges.
%    - Terminates: each pass either unifies at least one pair of Ids or leaves the set unchanged; the set is finite.
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Unify all Ids in a Key-group into the first; set Changed=true if the group had >1 Id.
%  Result: Rep is the first Id; each tail Id is unified with it.
%  Drives the outer fixpoint in merge_nodes/2.
%  Note: unifying Ids may instantiate variables inside Keys; a subsequent sort can reveal new duplicates.
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
%  Note: BA is a fresh class Id for B+A; AB=BA is consumed by rebuild//1 to alias classes. Rules never unify themselves.
%  Determinism: nondet over the worklist; at most one emission per matching node (prevents duplicate blow-up).
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  Restricts candidates to members of class(BC) via Index to avoid quadratic search over unrelated nodes.
%  Note: AB and ABC_ are fresh class Ids; ABC=ABC_ is consumed by rebuild//1 to alias. The rule only emits nodes/equalities; no unification here.
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
%  Neutral element of +/2: if class(B) contains the integer 0, emit A=AB.
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
%  Fold ground numeric additions (integers/floats) into a single constant.
%  Shrinks the search space by canonicalizing ground arithmetic; introduces fresh C and preserves AB as the class Id via C=AB.
%  Note: uses is/2 for evaluation; the rule only emits nodes/equalities and does not unify Ids.
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
%  Note: rules are pure producers (emit nodes and A=B); Id aliasing happens only in rebuild//1.
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
%  - Complexity: O(N log N) (group + tree build).
%  - Ids are variables and may alias; always rebuild after aliasing.
%  - Assumes Nodes are canonicalized by merge_nodes/2. Determinism: det.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce Matches (Key-Id items and (=)/2 equalities).
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
%  Apply Matches (Key-Id items and (=)/2 equalities) and canonicalize:
%    - exclude(unif, Matches, NewNodes): perform A=B unifications, drop equalities.
%    - push_back(NewNodes): schedule remaining Key-Id items.
%    - merge_nodes: canonicalize the graph.
%  Effects: only class-Id aliasing via (=)/2; logical and backtrackable. Equalities are consumed; no other mutation. Deduplication occurs only in merge_nodes/2.
%  Determinism: det.
%  Notes:
%    - unif/1 intentionally performs side-effect unification of Id variables; use only via exclude/3 here. This is the single place where (=)/2 is executed.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Apply Rules until a fixpoint (no new Key-Id items/equalities). See saturate/4 caveat on alias-only steps.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run at most MaxSteps iterations (non-negative integer or inf).
%  - Fixpoint: compares lengths before/after rebuild (post-merge_nodes/2).
%  - Alias-only steps do not change length; rules must eventually add/remove pairs.
%  Determinism: det driver; nondet arises only from Rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Worker. Threads the e-graph explicitly.
%  - MaxSteps: non-negative integer (use DCG wrapper for inf).
%  - Each iteration rebuilds the Id->Keys index because Id variables may alias.
%  - Fixpoint is length-based; alias-only progress is invisible.
%  Determinism: det driver; nondet comes only from Rules.
%  Notes:
%    - Rules must be pure producers (emit items and equalities only). Any unification they rely on should happen via rebuild//1.
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
%  Recognize A=B and perform the unification as a side effect.
%  Use with exclude/3 to apply equalities and drop them from a worklist.
%  Effects: intentionally unifies class Id variables; fails for non-(=)/2 items. Effects are logical and backtrackable.
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
%  Determinism: semidet.
%  Note: uses member/2 on Keys and thus can alias Id variables; use only for validation.
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
