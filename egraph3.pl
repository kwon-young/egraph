:- module(egraph, [add//2, union//2, saturate//1, saturate//2,
                   extract/4, extract//3]).

/** <module> egraph
E-graphs for Prolog terms where class identifiers are logic variables.
Each class Id is a logic variable that may only be aliased using (=)/2.
Compare Id variables by identity with (==) and never by name or print-name.

Nodes are an ordset of Key-Id pairs where Key is an atom, a variable, or F(Ids).
Keys preserve variable identity and are never alpha-renamed or normalized.
Ids are opaque logic variables and must not be inspected or compared by name.

Canonicalization keeps at most one Key-Id per Key and is done by merge_nodes/2.
Unifying Ids may instantiate variables inside Keys and the next merge collapses
any collisions.

Rules are pure producers that emit only Key-Id pairs and equalities A=B.
Rules must not inspect or bind Id variables and must not unify Keys.
Only rebuild//1 and merge_nodes/2 may alias Ids and must run after rules to
propagate effects and to re-canonicalize.

add//2 inserts a term as nodes and yields its class Id via DCG.
union//2 aliases two class Ids via DCG and then re-canonicalizes.
saturate//1 runs the fixed-point driver with an unbounded step budget.
saturate//2 runs the driver with an explicit bounded step budget.
extract//0 aliases each class Id to a representative Key via DCG.
extract/1 aliases each class Id to a representative Key in place.

saturate iterates make_index, match, rebuild, and merge until the node count
stabilizes and alias-only steps do not count as progress.

lookup/2 expects canonicalized input and non-canonical sets may fail spuriously.
Keys are variable-identity sensitive and variant-equal Keys with distinct
variables are intentionally treated as different Keys.

BUG: assoc//2 commits before rb_lookup/3 so when BC is absent the rule fails
instead of emitting nothing.
Intended behavior is to emit no output when BC is absent.

The goal of extract is to extract a concrete prolog term per class by
unifying each class Id with one representative Key.
Extraction is the last standard step of using an egraph and must not be
followed by rewriting or saturation.

Notes.
Use Id variables as mutable unique identifiers and restrict unification to
rebuild//1 and merge_nodes/2.
Do not inspect, print, or compare Id variables by name in user code or rules.
Portability note: the atom inf as an unbounded step in saturate//2 may be
non-portable across Prolog systems.
On such systems prefer a large integer bound passed to saturate//2.

Portability.
DCG wrappers for //2 nonterminals rely on SWI-Prolog DCG expansion that maps
them to predicates with two extra list arguments.
Other systems may require explicit wrappers for these DCG rules.
**/

:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

cost:attr_unify_hook(XCost, Y) :-
   (  get_attr(Y, cost, YCost)
   -> append(XCost, YCost, Cost),
      list_to_ord_set(Cost, Set),
      put_attr(Y, cost, Set)
   ;  var(Y)
   -> put_attr(Y, cost, XCost)
   ;  true
   ).
const:attr_unify_hook(XConst, Y) :-
   (  get_attr(Y, const, YConst)
   -> XConst =:= YConst
   ;  var(Y)
   -> put_attr(Y, const, XConst)
   ;  true
   ).

%! lookup(+Key-?Id, +Pairs) is semidet.
%  Find Id for Key in a canonical ordset of Key-Id pairs using (==) on Keys.
%  - Pre: Pairs canonical (run merge_nodes/2 after aliasing).
%  - Method: prune by standard order.
%  - Confirm Key identity with (==).
%  - Only the Id argument is bound.
%  - Determinism/Complexity: semidet; steadfast; O(N); no choice points.
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
   ;  ord_add_element(In, Node-Id, Out),
      (  compound(Node)
      -> Cost = Node
      ;  number(Node)
      -> put_attr(Id, const, Node),
         Cost = 1
      ;  Cost = 1
      ),
      put_attr(Id, cost, [Cost])
   ).

get(Name, Id, Value) :-
   get_attr(Id, Name, Value).

%! comm(+Node, +Index)// is nondet.
%  Commutativity of +/2: for (A+B)-AB emit B+A-BA and AB=BA without binding Ids.
%  Emits exactly two outputs in order: the commuted node and then the equality.
%  Models equality without in place rewrite and emits at most one variant.
%  Notes:
%  - BA is a fresh Id and AB is the original Id.
%  - The equality is consumed by rebuild//1 and aliases only Id variables.
%  - Rules must not inspect or bind Ids and may only emit nodes and A=B.
comm((A+B)-AB, _Nodes) ==>
   [B+A-BA, AB=BA].
comm((A*B)-AB, _Nodes) ==>
   [B*A-BA, AB=BA].
comm(_, _) ==> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of +/2: from (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  - Restrict to members of class(BC) via Index; may emit multiple triples (one per matching B+C member).
%  Index: rbtree Id -> [Keys]; rebuilt each iteration; read-only.
%  - BUG: A cut commits before rb_lookup/3, so when BC is absent the rule
%    fails instead of emitting nothing.
%  - Intended: emit no output when BC is absent in Index (see tests).
%  Notes:
%  - AB and ABC_ are fresh; unification is deferred to rebuild//1 (Ids only).
%  - The Id for BC confines the search; never unify Keys here.
%  - Rules must not inspect or bind Ids; only emit nodes and (=)/2 between Ids.
assoc((A+BC)-ABC, Index) ==>
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) ==> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of class(BC) with A fixed.
%  - Emit at most one triple per qualifying member; confine rewrites to the class.
%  Notes:
%  - Pure producer; must not inspect or bind Ids.
%  - Members are Keys from Index; unification happens later in rebuild//1 (Ids only).
%  Determinism: nondet over Members; tail-recursive; no side effects.
assoc_([(B+C) | Nodes], A, ABC) ==>
   {  put_attr(AB, cost, [A+B]),
      put_attr(ABC_, cost, [AB+C])
   },
   [A+B-AB, AB+C-ABC_, ABC=ABC_],
   assoc_(Nodes, A, ABC).
assoc_([(B*C) | Nodes], A, ABC) ==>
   {  put_attr(AB, cost, [A*B]),
      put_attr(ABC_, cost, [AB*C])
   },
   [A*B-AB, AB*C-ABC_, ABC=ABC_],
   assoc_(Nodes, A, ABC).
assoc_(_, _, _) ==> [].
%! reduce(+Node, +Index)// is semidet.
%  Neutral element of +/2: if class(B) contains integer 0, emit A=AB.
%  - Uses once/1 to avoid duplicates; match the integer 0 exactly with (==).
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Unification happens in rebuild//1 (Ids only); rules must not inspect or bind Ids.
%  - Use strict term equality (==) to match integer 0 and not 0.0.
%  Determinism: semidet; pure producer.
reduce(A+B-AB, _Index), get_attr(B, const, 0) ==>
   [A=AB].
reduce(A*B-AB, _Index), get_attr(B, const, 1) ==>
   [A=AB].
reduce(_*B-AB, _Index), get_attr(B, const, 0) ==>
   [B=AB].
reduce(_, _) ==> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold ground numeric sums for +/2 into a constant.
%  - Introduce C where VC is VA+VB; emit VC-C and C=AB.
%  Index: rbtree Id -> [Keys]; read-only.
%  Notes:
%  - Uses is/2; respects Prolog numeric semantics and mixed numeric types; pure
%    producer.
%  - Unification deferred to rebuild//1 (Ids only). Non-numeric members are skipped.
%  Determinism: nondet; no side effects; must not inspect or bind Ids.
constant_folding((A+B)-AB, _Index),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA+VB,
      put_attr(C, const, VC),
      put_attr(C, cost, [1])
   },
   [VC-C, C=AB].
constant_folding((A*B)-AB, _Index),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA*VB,
      put_attr(C, const, VC),
      put_attr(C, cost, [1])
   },
   [VC-C, C=AB].
constant_folding(_, _) ==> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply Rules to Node using Index; append outputs in rule order.
%  Each Rule is a DCG nonterminal Rule(Node,Index)//2.
%  - Node is Key-Id; rules may emit only Key-Id items and (=)/2 between Ids.
%  - Uses sequence//2 from library(dcg/high_order).
%  Index: rbtree Id -> [Keys]; read-only.
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
%  - Sorting and grouping use standard order and preserve variable identity.
%  - Result is rbtree(Id->[Keys]) with nonempty value lists; rebuild after any Id aliasing.
%  - Intended for the current iteration only; discard and rebuild after each rebuild//1 or merge.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist using Index; produce scheduled Matches (Key-Id items and (=)/2).
%  - Output order: worklist order then per-rule per-node order.
%  Impl: foldl/4 with rules//3.
%  Complexity: O(|Worklist|*|Rules| + |Matches|) plus per-Rule Index work.
%  Determinism: det; pure; steadfast (no Id unification here).
%  Notes:
%  - Rebuild Index after rebuild//1 (Ids may alias).
%  - Worklist is typically the current canonical Nodes.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).

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
%  Canonicalize to at most one pair per Key by unifying duplicate Ids and repeat until stable.
%  - Steps: sort -> group -> unify all Ids in each group with the first (representative).
%  - Only Id variables unify; Keys never do. Aliasing may instantiate variables inside Keys; the next pass collapses collisions.
%  Complexity: O(N log N) per pass; repeats while merges occur.
%  Notes:
%  - Out canonical (sorted; one Key-Id per Key).
%  - Terminates: each merge strictly decreases the number of distinct Id variables.
%  - Representative Id is the first after sorting; do not rely on it across backtracking.
%  - sort/2 and grouping use standard order and preserve variable identity.
%  - Rebuild any Id->[Keys] index after this (Ids are the map keys).

merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   merge_group(Groups, Tmp, false, Merged),
   (  Merged == true
   -> merge_nodes(Tmp, Out)
   ;  Out = Sort
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

merge_group([Node-[H | T] | Nodes], [Node-H | Worklist], In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Tmp = In
   ;  Tmp = true
   ),
   merge_group(Nodes, Worklist, Tmp, Out).
merge_group([], [], In, In).

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
rebuild([A=B | T], In, Out) :-
   A = B,
   rebuild(T, In, Out).
rebuild([N-Id | T], In, Out) :-
   rebuild(T, [N-Id | In], Out).
rebuild([], In, Out) :-
   merge_nodes(In, Out).
              
%! saturate(+Rules)// is det.
%  Iterate Rules to a length fixpoint (after rebuild/merge).
%  - Pure producer; emits only Key-Id and (=)/2.
%  - Alias-only steps (only A=B) do not count as progress.
%  Note: uses MaxSteps=inf as a sentinel and may be non-portable.
%  Prefer saturate//2 with a large integer bound on systems without inf.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Run up to MaxSteps iterations; stop early when length stabilizes (after rebuild/merge).
%  - MaxSteps: integer >= 0.
%  - Prefer a large integer over 'inf' on systems without arithmetic over inf.
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

extract(Id, Id, Cost, Nodes) :-
   extract(Id, Id, Cost, Nodes, Nodes).
extract(Id, Id, Cost, Nodes, Nodes) :-
   maplist([Node-NodeId, (Cost-Node)-NodeId]>>merge_cost(Node, Cost),
           Nodes, CostNodes),
   make_index(CostNodes, Index),
   rb_visit(Index, Pairs),
   foldl([NodeId-SubCostNodes, CostIn, CostOut]>>(
      keysort(SubCostNodes, Sort),
      member(Cost-NodeId, Sort),
      CostOut is CostIn + Cost
   ), Pairs, 0, Cost).
get_cost(Id, Cost) :-
   get_attr(Id, cost, Costs),
   foldl(merge_cost, Costs, inf, Cost).
merge_cost(Node, Cost) :-
   (  compound(Node)
   -> merge_cost(Node, inf, Cost)
   ;  Cost = 1
   ).
merge_cost(Cost, In, Out) :-
   (  compound(Cost)
   -> Cost =.. [_ | Ids],
      maplist(get_cost, Ids, Costs),
      sum_list([1 | Costs], RealCost)
   ;  RealCost = Cost
   ),
   Out is min(In, RealCost).

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
%  Build left-associated sum 1+2+...+N as a +(A,B) chain.
%  Domain: N >= 1.
%  Note: Fails when N < 1 because numlist/3 fails with low > high.
add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

%! example2(+N, -Expr) is det.
%  Build an addition chain and saturate with comm/assoc; prints counts to current output.
%  Sanity-check size growth vs. the closed form.
%  Note: on systems without saturate/3, call saturate/4 with an explicit bound.
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
example3(N, Expr, T) :-
   distinct(R, phrase((
      add(Expr, R),
      saturate([comm, assoc, reduce, constant_folding], N),
      extract(R, T)
   ), [], _)).
