:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs (equivalence graphs) for congruence closure on Prolog terms.

Summary
- Classes: each equivalence class is represented by a fresh Prolog variable (its class ID). Union is A=B (plain (=)/2). All effects are logical and fully backtrackable.
- Graph: an ordset of Key-Id pairs in standard term order. Key is any term (may contain variables). Id is the current class representative (a Prolog variable).
- Rules: DCGs that produce new nodes (Key-Id) and equalities (A=B). Saturation applies rules to a fixpoint.

Data model
- Nodes: ordset of Key-Id; canonicalization ensures at most one pair per distinct Key.
- Index: rbtree Id -> [Keys] rebuilt from canonicalized nodes for per-class access.

Execution model
- DCGs thread the e-graph as a difference list (In/Out).
- “Mutation” is unification of class ID variables; this can also instantiate variables inside Keys. Effects are logical, backtrackable, and non-destructive.

Identity and variants
- Membership uses standard term order; identity after ordering is tested with (==).
- No variant-normalization: keys that differ only by variable identity remain distinct.

Caveats
- merge_nodes/2 repeatedly sorts by Key, groups duplicates, and unifies IDs within each group until no change. Because unification of IDs can bind variables inside Keys, resorting may reveal new duplicates.
- The length-based fixpoint in saturate//2 ignores alias-only progress; rules must eventually add or remove Key-Id pairs.
- Class IDs are fresh Prolog variables (not atoms). Unifying IDs aliases classes and may instantiate variables inside Keys. No occurs-check is used; safe because IDs are never unified with compound terms.
- Validation with extract//0 can further alias IDs (member/2 can bind an ID). Use only for throwaway validation states, not for persisted graphs.

Notes on “mutable unique identifiers”
- Class IDs are plain Prolog variables used as mutable representatives. Unifying two IDs aliases the classes and may instantiate variables appearing inside Keys. All such effects are backtrackable.
- The rbtree index uses these variables as keys; always rebuild the index after any aliasing (this module does so per saturation step).

See also
- add//2, union//2, merge_nodes//0, saturate//2, extract//0.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Read-only membership/lookup in an ordset of Key-Val pairs (standard term order).
%  - Pairs must be a strictly ordered ordset; Key must be nonvar.
%  - Identity uses (==) after standard ordering; variable identity matters; no unification.
%  - Complexity: O(N) small-window linear scan (4/2/1 lookahead).
%  - Errors: if Key is var, compare/3 raises instantiation_error; lookup/2 never binds Key.
%  Determinism: semidet.
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
%  Insert Term and return its class Id; reuse Id if Key already exists.
%  - Compound: add subterms left-to-right; Key = F(ChildIDs) where ChildIDs are class IDs of subterms (congruence).
%  - Atomic (incl. variables): Key = Term.
%  Notes:
%    - Id is a fresh Prolog variable used as a mutable class representative. Union/rules may alias Ids by unification, which can also instantiate variables inside Keys; all effects are backtrackable.
%    - No canonicalization here; duplicates may be introduced. Use merge_nodes//0 to collapse duplicates.
%    - DCG state threads an ordset of Key-Id pairs (standard term order).
%  Determinism: det.
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
%  Ensure Node has a class Id; reuse existing Id if present, otherwise insert Node-Id.
%  Notes:
%    - In/Out are ordsets of Key-Id (standard order). Identity after ordering uses (==); no variant-normalization (variable identity matters).
%    - Unifying Ids elsewhere may bind variables inside Keys. Always re-canonicalize with merge_nodes/2 (or //0) after aliasing.
%  Determinism: det.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%  Alias classes by unifying IdA with IdB, then canonicalize.
%  Rationale: logic-variable unification provides a cheap, fully backtrackable union.
%  Notes:
%    - IdA/IdB must be class IDs obtained from add//2 or add_node/4.
%    - Unification may bind variables inside Keys; rules rely on this.
%    - Immediately calls merge_nodes//0 to collapse duplicates introduced by aliasing.
%    - Uses (=)/2 without occurs-check; safe because class IDs are fresh variables and never unified with compound terms.
%  Determinism: det.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG: canonicalize the threaded node set (In/Out).
%! merge_nodes(+In, -Out) is det.
%  Sort by Key, group equal Keys, unify all Ids in each group into the first; repeat while any group changed.
%  Complexity: O(N log N) per pass (sort + group); repeats until a fixpoint.
%  Notes:
%    - Unifying Ids can bind variables inside Keys; resorting can reveal new duplicates, hence multiple passes.
%    - Leaves exactly one Key-Id pair per distinct Key at fixpoint.
%  Determinism: det.
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
%  Matches only +(A,B) nodes; emits at most one result per match.
%  Determinism: nondet over the worklist; at most one emission per matching Node (prevents duplicate blow‑up).
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity of (+): for (A+(B+C))-ABC emit (A+B)-AB, (AB+C)-ABC_, and ABC=ABC_.
%  Candidate BCs are restricted to class(BC) via Index to avoid quadratic search over unrelated nodes.
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
%  Eliminates the neutral element; once/1 avoids duplicates.
%  Note: checks for the integer 0 using (==); 0.0 does not qualify; only Keys already bound to 0 qualify.
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
%  Helper: for numeric VB in class(B) compute VC is VA+VB, then emit VC-C and C=AB.
%  Builds the folded constant lazily while keeping AB as the class Id.
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
%  Apply all DCG rules to Node with access to Index.
%  Rules is a list of DCG callables Rule(Node, Index)//; backtracks over Rules.
%  Notes:
%    - Rules should be pure producers; unification/merging happens in rebuild//1.
%  Determinism: nondet over Rules; output items are appended to the DCG stream.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule on Node.
%  Rule is a callable DCG of arity 3: Rule(Node, Index)//.
%  Determinism: follows the determinism of Rule/3.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree Index mapping Id -> [Keys] from an ordset of Key-Id pairs.
%  Enables fast per-class access during rule matching.
%  Complexity: O(N log N) overall (grouping + tree build).
%  Notes:
%    - IDs reflect current aliasing after unions; IDs are Prolog variables used as map keys. Always rebuild the index after aliasing.
%    - Each value lists all concrete Keys for that class.
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
%  Note: purely structural; no deduplication is performed.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply equalities (A=B) by unification, enqueue new nodes, then canonicalize.
%  Steps:
%    - exclude(unif, Matches, NewNodes): unify and drop (=)/2 items.
%    - push_back(NewNodes): append Key-Id items to the DCG output.
%    - merge_nodes//0: canonicalize.
%  Effects are logical and backtrackable (via variable aliasing).
%  Notes:
%    - Equalities are consumed (not re-enqueued); only Node-Id items flow forward.
%    - Alias-only steps are invisible to the length-based fixpoint in saturate//2 unless they add/remove pairs.
%    - Unifying class IDs may instantiate variables appearing inside Keys; merge_nodes//0 re-canonicalizes after such aliasing.
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
%  Fixpoint compares lengths before/after rebuild/1 (after merge_nodes/2).
%  Caveat: alias-only steps do not change the length; rules must eventually add/remove pairs.
%  Determinism: det driver; nondeterminism comes only from rules.
%! saturate(+Rules, +MaxSteps, +In, -Out) is det.
%  Underlying 4-ary predicate for saturate//2.
%  Threads the e-graph difference list explicitly (In/Out).
%  MaxSteps must be a non-negative integer; use saturate//1 or saturate//2 with inf if you want an unbounded DCG loop.
%  Note: length-based fixpoint; pure ID aliasing with no net pair change is not detected as progress. Use a bounded MaxSteps if rules can cycle without adding/removing pairs.
%  Implementation note: rebuilds the Id->Keys index on every iteration because ID variables may alias.
%  Note: do not pass the atom inf to this 4-ary predicate; the guard uses arithmetic comparison.
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
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Return the current nodes as Nodes (no validation).
%  Pairs with extract//0, which performs a validation pass.
%  Recommendation: prefer this in user code to avoid identifier mutation during validation.
%  Determinism: det.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  DCG variant: validate graph invariants after saturation.
%  Invariant: after grouping Id→Keys, each Id-group must have at least one concrete Key.
%  Warning: uses member(Id, Keys), which can bind class ID variables; use only for validation on throwaway states or under backtracking (not for persisted states).
%  Note: may further alias IDs if Keys contain those IDs; do not run on persisted graphs or states that must remain unchanged.
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
