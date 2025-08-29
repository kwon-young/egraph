:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graphs for term equivalence using Prolog logic variables as class identifiers.

Overview
- Each equivalence class is represented by a logic variable Id; union is plain unification (=)/2 on Ids.
- The e-graph is an ordset (list kept in standard term order) of Key-Id pairs; Key is a term (possibly compound), Id is a var.
- Rules are DCGs that emit new nodes (Key-Id) and equalities (A=B); saturation applies rules to a fixpoint.

Key points
- After unifying Ids, multiple pairs may share the same Key while Ids are aliases; merge_nodes/2 canonicalizes by grouping on Key and unifying all Ids in the group, iterating to a fixpoint.
- The Index (an rbtree) maps each class Id to the list of concrete Keys in that class; rules can target classes efficiently.
- DCG nonterminals thread the e-graph as a difference list of pairs (In/Out).
- Key identity for set operations uses standard term order; exact identity tests use (==). Variants with distinct variables are distinct Keys by design.

Notes
- Calling nonterminals like merge_nodes//0 inside a DCG reuses the same In/Out pair (i.e., merge_nodes/2 is invoked on the threaded state).
- Logic variables as Ids make unification the only “mutation”. All effects are undone by backtracking, so the design stays purely logical despite in-place unions.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Find Val for Key in an ordset of Key-Val pairs with fewer comparisons.
%  Why: micro-optimised linear search that peeks 4/2/1 items to cut compares; returns Val without touching the set.
%  Complexity: O(N) worst-case; improves constants vs. naive member/2 scans.
%  Determinism: semidet — succeeds once; fails if Key absent.
%  Requirements: Pairs is a strictly ordered ordset (standard term order). Identity uses (==) after ordering via compare/3; the set is not rebuilt.
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
%  Add Term to the e-graph and return its class Id (creating or reusing it).
%  Why: structural interning — subterms are added first and their class Ids become the children of the node key; ensures maximal sharing and congruence.
%  Behaviour: compound Terms are decomposed using (=..)/2; Node =.. [F|Ids] where Ids are the class Ids of arguments.
%  Notes: Id is a logic variable that may later be unified by unions; if Term already exists, its existing Id is reused.
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
%  Ensure Node has a class Id in the ordset; reuse the existing Id if present, otherwise insert Node-Id.
%  Why: the Id variable is the class representative; reusing it preserves class identity across insertions.
%  Notes: In/Out are ordsets of Node-Id pairs (standard term order). Key identity uses (==) after ordering; variants with distinct variables are distinct Keys. Does not canonicalize or merge classes.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%  Unify two class Ids and then canonicalize the e-graph to remove duplicates caused by aliasing.
%  Why: unification is the cheapest “mutable” union in Prolog.
%  Notes:
%  - IdA/IdB must be class Ids (logic variables) returned by add//2 or add_node/4.
%  - Unifying Ids may bind variables occurring inside Keys indirectly; this is intentional and relied upon.
%  - Triggers merge_nodes//0 to canonicalize after the union.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes(+In, -Out) is det.
%  Canonicalize the node set after unions.
%  Why: after Id unifications, multiple Key-Id pairs can share a Key; grouping by Key and unifying all Ids in each group collapses duplicates; repeats to a fixpoint.
%  Complexity: O(N log N) per pass due to sort/2; repeated until stable.
%  Notes:
%  - Uses foldl/5 with a boolean “changed” accumulator; the call only succeeds if any group had >1 Id, driving the outer recursion.
%  - Only one pair per Key remains; all Ids in that Key’s group are unified with the first.
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
%  Result: Rep is the first Id, with each tail Id unified to it.
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
%  Notes: matches only +(A,B) nodes.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for (+): for (A+(B+C)) emit ((A+B)+C) and equality.
%  Why: explore rebracketings that already exist in the target class to avoid quadratic blind search.
%  Notes: requires that the class of BC is present in Index (lookup by the Id of BC).
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
%  Why: eliminates neutral elements; once/1 limits duplicate emissions.
reduce(A+B-AB, Index) -->
   {  rb_lookup(B, Nodes, Index),
      once((member(Node, Nodes), Node == 0))
   },
   !,
   [A=AB].
reduce(_, _) --> [].
%! constant_folding(+Node, +Index)// is nondet.
%  Fold numeric additions into a single constant.
%  Why: shrink the search space early by canonicalizing ground arithmetic; preserves the class Id of the sum.
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
%  Why: construct the folded constant lazily; keep AB as the class Id.
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
%  Notes: Rules is a list of DCGs of the form Rule(Node, Index)//.
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule on Node.
%  Why: decouple the saturation engine from concrete rewrites.
%  Notes: Rule is a callable DCG of arity 3: Rule(Node, Index)//.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree mapping Id -> [Nodes] from Key-Id pairs.
%  Why: fast per-class access when matching rules.
%  Complexity: O(N log N) overall (sorting/grouping + tree build).
%  Notes:
%  - Nodes must be an ordset of Key-Id pairs.
%  - Id keys in the rbtree reflect current aliasing (after any unions).
%  - Each value is the list of concrete Keys known for that class.
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
push_back(L), L --> [].
%! rebuild(+Matches)// is det.
%  Apply equalities (by unification), enqueue new nodes, then canonicalize.
%  Why: maintain a normalized e-graph while growing it and integrate A=B edges immediately.
%  Details: uses exclude/3 with unif/1 to perform A=B side effects and drop them from the worklist; only (Key-Id) items are queued.
%  Note: merge_nodes//0 is invoked as a DCG nonterminal; this reuses merge_nodes/2 on the same (In,Out).
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
%! saturate(+Rules)// is det.
%  Saturate with Rules until a fixpoint.
%  Why: iterate rule application until the graph stops growing.
saturate(Rules) -->
   saturate(Rules, inf).
%! saturate(+Rules, +MaxSteps)// is det.
%  Saturate for at most MaxSteps iterations (inf for unbounded).
%  Why: bound the search when desired while preserving convergence checks.
%  Notes:
%  - Fixpoint is detected by comparing lengths before/after rebuild/1 (after merge_nodes), relying on canonicalization to remove dups.
%  - Caveat: the size-based check may miss further rewrites if Id-unifications change only the Index but not the number of pairs; the bundled rules always add/remove pairs when such changes matter.
%  - Nondeterminism only comes from the rules; the driver is deterministic.
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
%  Why: used with exclude/3 in rebuild//1 to apply equalities and drop them from the worklist.
%  Note: this intentionally mutates class IDs via unification; it fails for non-(=)/2 items.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Predicate variant: return the current nodes as Nodes (no validation).
%  Why: pair with extract//0 for validation in DCG contexts.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract//0 is det.
%  DCG variant: validate that each equivalence class contains its Key.
%  Why: ensures for every group Key-Ids that Key ∈ Ids.
%  Notes: Fails if invariants are broken; useful as a sanity check after saturation.
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   extract_node(Groups).
%! extract_node(+Groups) is semidet.
%  True if for every group Key-Members, Key ∈ Members.
%  Why: minimal consistency check for a well-formed extraction.
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
