:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs for congruence closure over Prolog terms. Equivalence classes are identified by fresh logic variables (class Ids).

Summary
- Classes: every class Id is a distinct logic variable; unions are performed by unification (A=B). Effects are logical and fully backtrackable.
- Graph: ordset of Key-Id pairs (standard term order). Key is any Prolog term (may contain variables); Id is the class variable.
- Rules: DCGs that emit new nodes (Key-Id) and equalities (A=B). Saturation iterates rules to a fixpoint.

Data
- Nodes: ordset of Key-Id; canonicalization keeps at most one pair per Key.
- Index: rbtree Id -> Keys (list) for per-class access during rule matching.

Execution model
- All DCGs thread the graph as a difference list (In/Out).
- “Mutation” is by unifying class Id variables; this can also bind variables occurring inside Keys. Effects are logical and backtrackable.

Identity and variants
- Ordering/membership use standard term order; exact identity checks use (==) only after ordering.
- Keys that differ only by variable identity are deliberately distinct (no variant normalization).

Notes
- merge_nodes/2: sort by Key, group, unify all Ids per group with the first; repeat while any group changed.
- Nonterminals (e.g., merge_nodes//0) operate on the same threaded state.
- Pitfall: the length-based fixpoint in saturate//2 does not observe alias-only progress; rules must eventually add/remove Key-Id pairs to make progress.
- Pitfall: class Ids are logic variables (not atoms); unification can alias classes and bind variables inside user terms.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Lookup Val for Key in an ordset of Key-Val pairs (ordered by standard term order).
%  - Search: small-window linear scan with 4/2/1 lookahead (no tree lookup).
%  - Requires: Pairs is a strictly ordered ordset; Key must be nonvar.
%  - Equality: after ordering, uses (==) for exact identity; succeeds at most once.
%  - Complexity: O(N) worst case; does not allocate on success (unifies Val with the stored value).
%  - Note: a var Key will throw in compare/3; this predicate never binds Key.
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
%  Insert Term and return its class Id; reuse the existing Id if Key already exists.
%  - Compound: add subterms first; the inserted Key is F(ChildIds) where ChildIds are the class Ids of subterms (congruence by construction).
%  - Atomic: Key = Term.
%  Notes:
%    - Id is a logic variable used as a mutable class identifier; unions/rules may alias classes via unification.
%    - Threads the e-graph ordset via DCGs. No canonicalization here; use merge_nodes//0.
%    - Subsequent Id unifications can bind variables occurring inside Keys.
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
%    - In/Out are ordsets of Key-Id (standard term order).
%    - Identity uses (==) only after ordering; variants that differ only by variable identity are distinct Keys.
%    - Later Id unifications may bind variables inside Keys; merge_nodes/2 re-canonicalizes.
%    - Does not collapse duplicates introduced by Id aliasing; call merge_nodes/2 or merge_nodes//0 to canonicalize.
%  Determinism: det (exactly one reuse or insert).
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%  Unify two class Ids (alias classes), then canonicalize the e-graph.
%  Rationale: logic-variable unification provides a cheap, fully backtrackable union.
%  Notes:
%    - IdA/IdB must be class Ids obtained from add//2 or add_node/4.
%    - Unifying Ids may bind variables inside Keys; rules rely on this.
%    - Immediately calls merge_nodes//0 to collapse duplicate Key-Id pairs introduced by aliasing.
%    - Uses (=)/2 (no occurs-check); with fresh class vars this is safe and fully backtrackable.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG: canonicalize the threaded node set (In/Out).
%! merge_nodes(+In, -Out) is det.
%  Canonicalize Nodes after Id unifications: sort, group by Key, unify all Ids per group with the first; repeats while any group changed.
%  Complexity: O(N log N) per pass; repeats to a fixpoint.
%  Notes:
%    - The pass sets a change flag; recursion continues while true.
%    - Id unifications may bind variables inside Keys; re-sorting can expose new duplicates.
%    - Leaves exactly one Key-Id pair per distinct Key.
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
%  Determinism: det.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity of (+): for (A+B)-AB emit B+A-BA and AB=BA.
%  Models equality without destructive rewrites; both orders share the class.
%  Matches only +(A,B) nodes; emits at most one pair per match.
%  Determinism: nondet over the worklist; at most one emission per matching Node.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of (+): for (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  Candidates are limited to the class of BC (via Index) to avoid quadratic search over unrelated nodes.
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
%  Unit of (+): if class(B) contains 0, emit A=AB.
%  Eliminates neutral elements; once/1 limits duplicates.
%  Note: checks for the integer 0 using (==); only Keys already bound to the integer 0 qualify.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold numeric additions (integers/floats) into a single constant.
%  Shrinks the search space by canonicalizing ground arithmetic; preserves AB as the class Id via C=AB.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Helper: pick numeric VA in class(A), then search class(B) for numeric VB.
%  Staged search avoids building pairs eagerly.
constant_folding_a([VA | ANodes], B, AB, Index) -->
   (  {number(VA)}
   -> {rb_lookup(B, BNodes, Index)},
      constant_folding_b(BNodes, VA, AB, Index)
   ;  []
   ),
   constant_folding_a(ANodes, B, AB, Index).
constant_folding_a([], _, _, _) --> [].
%! constant_folding_b(+ClassB, +VA, -AB, +Index)// is nondet.
%  Helper: for numeric VB in class(B) compute VC is VA+VB, then emit VC-C and C=AB.
%  Builds the folded constant lazily while keeping AB as the class Id.
%  Note: arithmetic uses is/2; types follow Prolog's numeric tower.
constant_folding_b([VB | BNodes], VA, AB, Index) -->
   (  {number(VB)}
   -> {VC is VA + VB},
      [VC-C, C=AB]
   ;  []
   ),
   constant_folding_b(BNodes, VA, AB, Index).
constant_folding_b([], _, _, _) --> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply all DCG rules to Node with access to Index.
%  Rules is a list of DCG callables Rule(Node, Index)//; backtracks over Rules.
%  Notes:
%    - Rules should be pure producers; unification/merging happens in rebuild//1.
%  Determinism: nondet over Rules; output is appended to the DCG stream.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule on Node.
%  Rule is a callable DCG of arity 3: Rule(Node, Index)//.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree Index mapping Id -> [Keys] from an ordset of Key-Id pairs.
%  Enables fast per-class access during rule matching.
%  Complexity: O(N log N) overall (grouping + tree build).
%  Notes:
%    - Ids reflect current aliasing after unions.
%    - Each value lists all concrete Keys for that class.
%    - Assumes Nodes are canonicalized by merge_nodes/2 to avoid duplicates.
%    - group_pairs_by_key/2 sorts internally; Nodes need not be pre-sorted by Id.
%    - Uses transpose_pairs/2 (library(pairs)).
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce new matches (nodes and equalities).
%  Central collection phase before rebuilding the graph. Worklist is the current node set (ordset of Key-Id pairs).
%  Determinism: det given Rules/Worklist/Index; output is a (possibly empty) list.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  DCG trick: append List at the end of the current output.
%  Schedules newly discovered items after the current worklist (O(1) via difference lists).
%  Note: purely structural; no deduplication is performed.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply equalities (A=B) by unification, enqueue new nodes, then canonicalize.
%  Steps:
%    - exclude(unif, Matches, NewNodes): unify and drop (=)/2 items.
%    - push_back(NewNodes): append Key-Id items to the DCG output.
%    - merge_nodes//0: canonicalize.
%  Effects are logical and backtrackable (via variable aliasing).
%  Note: equalities are consumed (not re-enqueued); only Node-Id items flow forward.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Saturate with Rules until no new nodes/equalities are produced (fixpoint).
%  Note: see saturate/4 for the length-based fixpoint caveat.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Saturate for at most MaxSteps iterations (use inf for unbounded).
%  Fixpoint uses lengths before/after rebuild/1 (after merge_nodes/2).
%  Caveat: length-only checks ignore alias-only steps; rules must eventually add/remove pairs to make progress.
%  Determinism: det driver; nondeterminism comes only from rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Underlying 4-ary form used by DCG expansion of saturate//2.
%  Threads the e-graph difference list explicitly (In/Out).
%  Note: length-based fixpoint; pure Id aliasing with no net pair change is not detected as progress.
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
%  Notes: intentionally mutates class Ids via unification; fails for non-(=)/2 items. Effects are logical and backtrackable.
%  Determinism: semidet; succeeds once on (=)/2, fails otherwise.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Return the current nodes as Nodes (no validation).
%  Pairs with extract//0, which performs a validation pass.
%  Recommendation: prefer this predicate in user code to avoid identifier mutation during validation.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  DCG variant: validate graph invariants after saturation.
%  Invariant: after grouping Id→Keys, each Id-group must have at least one concrete Key.
%  Warning: uses member(Id, Keys), which can bind class Id variables; use only for validation on throwaway states or under backtracking (not for persisted states).
%  Note: this validation can alias Ids further if Keys contain those Ids; do not run on persisted graphs.
%! extract(+Nodes, -Nodes) is semidet.
%  Underlying helper for extract//0; succeeds iff each Id-group has a concrete Key.
%  Note: arguments are typically the same variable to avoid copying; do not rely on side effects.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one concrete Key; fails otherwise.
%  Minimal consistency check; may bind Ids via member/2 (use only for validation).
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
%  Build right-associated sum 1+2+...+N (as a +(A,B) term chain).
add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

%! example2(+N, -Expr) is det.
%  Build an addition chain and saturate with comm/assoc; prints counts.
%  Sanity-check size growth vs. the closed form.
example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add(Expr, _), [], G),
   time(saturate([comm, assoc], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

%! example3(+N, +Expr, -R) is nondet.
%  Enumerate possible results R after saturating with all rules, then validate via extract//0.
%  Determinism: nondet over alternative extractions R.
example3(N, Expr, R) :-
   distinct(R, phrase((
      add(Expr, R),
      saturate([comm, assoc, reduce, constant_folding], N),
      extract
   ), [], _)).
