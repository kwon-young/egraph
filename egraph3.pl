:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs for term equivalence with logic variables as class identifiers.

Overview
- A class is represented by a fresh logic variable Id. Union is IdA=IdB (pure, backtrackable).
- The e-graph is an ordset (standard-term-ordered list) of Key-Id pairs. Key is a concrete term; Id is the class var.
- Rules are DCGs that emit new nodes (Key-Id) and equalities (A=B). Saturation applies rules to a fixpoint.

Key properties
- Unifying Ids may create duplicate Keys with aliased Ids. merge_nodes/2 groups by Key and unifies all Ids per group until stable.
- The Index (rbtree) maps each Id to the list of Keys in that class for fast per-class queries during rule matching.
- All DCGs thread the e-graph as a difference list of pairs (In/Out).

Identity and mutability
- Set membership and ordering use standard term order; exact identity checks use (==) after ordering.
- Variants are distinct Keys by design (variables in Keys matter).
- “Mutation” is only via unification of Ids; this can also bind variables occurring inside Keys. All effects are logical and backtrackable.

Notes
- Calling a nonterminal like merge_nodes//0 inside a DCG acts on the same threaded state (it expands to merge_nodes/2 on In/Out).
- Some rules rely on side effects of Id unification to propagate equalities through Keys without destructive updates.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Find Val for Key in an ordset of Key-Val pairs using a small-window linear search (4/2/1 lookahead) to reduce comparisons.
%  Why: micro-optimised scan that improves constants vs. naive member/2; does not rebuild or reorder the set.
%  Complexity: O(N) worst-case.
%  Determinism: semidet — succeeds at most once; fails if Key absent.
%  Requirements: Pairs is a strictly ordered ordset (standard term order). Identity uses (==) after ordering via compare/3.
%  Precondition: Key must be ground (or otherwise comparable) for compare/3; passing a variable will error.
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
%  Insert Term and return its class Id (create if absent).
%  - Compound Terms: subterms are added first; their class Ids become arguments of the node Key (congruence by construction).
%  - Atomic Terms: Key=Term.
%  Notes:
%    - Id is a fresh logic variable used as the mutable class identifier; later union/2 may unify it with others.
%    - DCG threads the e-graph state (In/Out).
%    - If Term's Key already exists, Id is unified with the existing class Id (no duplicate is inserted).
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
%  Why: preserves class identity when the same Node is seen again.
%  Notes:
%    - In/Out are ordsets of Key-Id pairs (standard term order).
%    - Key identity uses (==) only after ordering; variants with different variables are distinct Keys.
%    - Node may contain variables inside Keys; later unifications can affect ordering — merge_nodes/2 re-canonicalizes.
%    - No merging is done here; call merge_nodes/2 after unions.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%  Unify two class Ids and then canonicalize the e-graph.
%  Why: logic-variable unification is the cheapest, fully backtrackable “union”.
%  Notes:
%    - IdA/IdB must be class Ids from add//2 or add_node/4.
%    - Unifying Ids may also bind variables inside Keys; rules depend on this.
%    - Invokes merge_nodes//0 to collapse duplicates caused by aliasing.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes//0 is det.
%  DCG variant: canonicalize the threaded node set (In/Out).
%! merge_nodes(+In, -Out) is det.
%  Canonicalize the node set after Id unifications.
%  How: sort/2, group by Key, unify all Ids in each group with the first, then repeat until stable.
%  Complexity: O(N log N) per pass; repeats to a fixpoint.
%  Notes:
%    - Uses a boolean “changed” accumulator to drive the outer recursion.
%    - Unifications can bind variables inside Keys; re-sorting may reveal new duplicates, requiring another pass.
%    - Leaves exactly one Key-Id pair per distinct Key.
%    - Implementation detail: uses foldl/5 to rebuild Key→Rep pairs while threading a Changed flag.
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Unify all Ids in a group into the first and signal if anything changed.
%  Why: propagates equivalence within a Key-group and drives the outer fixpoint in merge_nodes/2.
%  Result: Rep is the first Id; each tail Id is unified with it.
%  Notes: Changed is true iff the group had more than one Id (T \== []).
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for (+): emit node B+A-BA and equality AB=BA.
%  Why: model equalities without destructive rewrites; both orders inhabit the same class.
%  Notes: matches only +(A,B) nodes; may emit at most one pair per matching node.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for (+): for (A+(B+C)) emit ((A+B)+C) and equality.
%  Why: explore rebracketings that already exist in the target class to avoid quadratic blind search.
%  Notes: requires that the class of BC is present in Index (lookup by the Id of BC); confines candidates to the current class.
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
%! assoc_(+Members, +A, -ABC)// is nondet.
%  Helper for assoc//2: iterate members of the class of BC.
%  Why: confines candidate rewrites to the current equivalence class.
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].
%! reduce(+Node, +Index)// is semidet.
%  Unit for (+): if class of B contains 0, emit A=AB.
%  Why: eliminate neutral elements; once/1 limits duplicate emissions.
%  Note: checks for the integer 0 using (==); only keys already bound to 0 qualify.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold numeric additions into a single constant.
%  Why: shrink the search space early by canonicalizing ground arithmetic; preserves the class Id of the sum by equating the folded constant with AB.
constant_folding((A+B)-AB, Index) -->
   !,
   { rb_lookup(A, ANodes, Index) },
   constant_folding_a(ANodes, B, AB, Index).
constant_folding(_, _) --> [].
%! constant_folding_a(+ClassA, +B, -AB, +Index)// is nondet.
%  Helper: pick numeric VA from class(A) and search class(B) for VB.
%  Why: staged search avoids building pairs eagerly.
constant_folding_a([VA | ANodes], B, AB, Index) -->
   (  {number(VA)}
   -> {rb_lookup(B, BNodes, Index)},
      constant_folding_b(BNodes, VA, AB, Index)
   ;  []
   ),
   constant_folding_a(ANodes, B, AB, Index).
constant_folding_a([], _, _, _) --> [].
%! constant_folding_b(+ClassB, +VA, -AB, +Index)// is nondet.
%  Helper: for numeric VB in class(B) emit VC where VC is VA+VB.
%  Why: construct the folded constant lazily; keep AB as the class Id by emitting C=AB.
constant_folding_b([VB | BNodes], VA, AB, Index) -->
   (  {number(VB)}
   -> {VC is VA + VB},
      [VC-C, C=AB]
   ;  []
   ),
   constant_folding_b(BNodes, VA, AB, Index).
constant_folding_b([], _, _, _) --> [].

%! rules(+Rules, +Index, +Node)// is nondet.
%  Apply all rules (DCGs) to Node with access to Index.
%  Why: treat rules as pluggable DCGs for extensibility.
%  Notes: Rules is a list of DCGs of the form Rule(Node, Index)//. The driver backtracks over rules.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule on Node.
%  Why: decouple the saturation engine from concrete rewrites.
%  Notes: Rule is a callable DCG of arity 3: Rule(Node, Index)//.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree Index mapping Id -> [Keys] from the ordset Nodes.
%  Why: enables fast per-class access when matching rules.
%  Complexity: O(N log N) overall (sorting/grouping + tree build).
%  Notes:
%    - Nodes must be an ordset of Key-Id pairs.
%    - Ids reflect current aliasing after any unions.
%    - Each value lists all concrete Keys known for that class.
%    - Assumes Nodes have been canonicalized by merge_nodes/2; otherwise per-class lists may include duplicates.
make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

%! match(+Rules, +Worklist, +Index, -Matches) is det.
%  Run Rules over Worklist to produce new matches (nodes/equalities).
%  Why: central collection phase before rebuilding the graph.
match(Rules, Worklist, Index, Matches) :-
   foldl(rules(Rules, Index), Worklist, Matches, []).
%! push_back(+List)// is det.
%  DCG trick to append a list of items at the end of the current output.
%  Why: schedule newly discovered items after the current worklist.
%  Effect: O(1) DCG append via difference lists.
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply equalities (by unification), enqueue new nodes, then canonicalize.
%  Details:
%    - exclude(unif, Matches, NewNodes) performs A=B unifications as a side effect and drops them.
%    - Only (Key-Id) items are queued via push_back//1, then merge_nodes//0 runs.
%  Note: effects are logical and backtrackable.
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Saturate with Rules until no new nodes/equalities are produced.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Saturate for at most MaxSteps iterations (use inf for unbounded).
%  Fixpoint check: compares sizes before/after rebuild/1 (after merge_nodes/2).
%  Caveat: size-only check may miss changes that affect only Index; bundled rules always add/remove pairs when it matters.
%  Determinism: deterministic driver; nondeterminism comes only from rules.
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
%  Notes: intentionally mutates class Ids via unification; fails for non-(=)/2 items. Side-effects are logical and backtrackable.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Predicate variant: return the current nodes as Nodes (no validation).
%  Why: pair with extract//0 for validation in DCG contexts.
%  Recommendation: prefer this predicate in user code to avoid identifier mutation.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is semidet.
%  DCG variant: validate graph invariants after saturation.
%  Intended invariant: after grouping Id→Keys, each Id-group must have at least one concrete Key.
%  Note: The current check uses member(Id, Keys), which unifies Id with a Key and can bind Ids; use only for validation on throwaway states or under backtracking.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True iff every Id-group has at least one concrete Key; fails otherwise.
%  Why: minimal consistency check; may bind Ids via member/2.
%  Note: member/2 here can bind the group Id to a Key term, logically mutating identifiers; avoid outside validation.
extract_node([Node-Nodes | Groups]) :-
   member(Node, Nodes),
   extract_node(Groups).
extract_node([]).

%! example1(-G) is det.
%  Small demo: add a, f(f(a)), union them, and add f^4(a); returns graph.
example1(G) :-
   phrase((
      add(a, A),
      add(f(f(a)), FFA),
      union(A, FFA),
      add(f(f(f(f(a)))), _FFFFA)
   ), [], G).


%! add_expr(+N, -Expr) is det.
%  Build right-associated sum 1+2+...+N.
add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

%! example2(+N, -Expr) is det.
%  Build an addition chain and saturate with comm/assoc; prints counts.
%  Why: sanity-check size growth vs. closed form.
example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add(Expr, _), [], G),
   time(saturate([comm, assoc], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

%! example3(+N, +Expr, -R) is nondet.
%  Enumerate possible results R after saturating with all rules, then
%  validating extraction.
example3(N, Expr, R) :-
   distinct(R, phrase((
      add(Expr, R),
      saturate([comm, assoc, reduce, constant_folding], N),
      extract
   ), [], _)).
