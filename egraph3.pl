:- module(egraph, [add//2, union//2, saturate//1, saturate//2, extract/1, extract//0]).

/** <module> egraph
E-graph for term equivalence using Prolog variables as class IDs.

Why:
- Prolog variables act as mutable unique identifiers for equivalence classes; unification (=/2) performs union.
- Nodes are stored as an ordered set of Key-Id pairs to deduplicate and make merging cheap.
- Rewrite rules are expressed as DCGs that emit new nodes and equalities; saturation applies them until a fixpoint.

Notes:
- After unions, multiple nodes may collapse to the same key with aliased Ids; merge_nodes/2 resolves this to a canonical set.
- Indexes map class IDs to member nodes for targeted rule application.
*/


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

%! lookup(+Key-?Val, +Pairs) is semidet.
%  Lookup by key in an ordset of Key-Val pairs with fewer compares.
%  Why: minimize constant factors during saturation by peeking 4/2/1 items
%  at a time and comparing only on keys; Val is returned without touching
%  the structure of the set.
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
%  Add a term to the e-graph and return its class Id.
%  Why: structural interning — subterms are added first and their class
%  IDs become the children of the node key; ensures maximal sharing.
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
%  Ensure Node has a unique class Id in the ordset; reuse if present.
%  Why: the Id variable is the equivalence-class representative; reusing
%  it preserves class identity across insertions.
add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

%! union(+IdA, +IdB)// is det.
%  Union two equivalence classes by unifying their Id variables, then
%  request a structural merge to remove duplicates caused by aliasing.
%  Why: unification is the cheapest "mutable" union in Prolog.
union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

%! merge_nodes(+In, -Out) is det.
%  Canonicalize the node set after unions.
%  Why: after Id unifications, multiple Key-Id pairs may share keys;
%  grouping by key and unifying Ids collapses duplicates; repeat until
%  no changes remain to reach a fixpoint.
merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
%! merge_group(+Key-Ids, -Key-Rep, +Changed0, -Changed) is det.
%  Unify all Ids in a group into the first and signal if anything changed.
%  Why: propagates equivalence within a key-group and drives the outer
%  fixpoint in merge_nodes/2.
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

%! comm(+Node, +Index)// is nondet.
%  Commutativity for (+): emit B+A with equality BA=AB.
%  Why: model equalities without destructive rewrites; both orders inhabit
%  the same class.
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].
%! assoc(+Node, +Index)// is nondet.
%  Associativity for (+): for (A+(B+C)) emit ((A+B)+C) and equality.
%  Why: explore rebracketings that already exist in the target class to
%  avoid quadratic blind search.
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
%  Why: shrink the search space early by canonicalizing ground arithmetic.
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
rules(Rules, Index, Node) -->
   sequence(rule(Index, Node), Rules).
%! rule(+Index, +Node, :Rule)// is nondet.
%  Meta-call a single DCG rule on Node.
%  Why: decouple the saturation engine from concrete rewrites.
rule(Index, Node, Rule) -->
   call(Rule, Node, Index).

%! make_index(+Nodes, -Index) is det.
%  Build an rbtree mapping Id -> [Nodes] from Key-Id pairs.
%  Why: fast per-class access when matching rules.
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
%  Drop trivial equalities, enqueue new items, then canonicalize nodes.
%  Why: maintain a normalized e-graph while growing it.
%  Note: merge_nodes/0 is called as a DCG nonterminal; in this context
%  it relies on the same In/Out list threading as merge_nodes/2.
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
%  True iff Eq is an already-true equality A=B.
%  Why: used with exclude/3 to discard redundant equalities.
unif(A=B) :- A=B.

%! extract(-Nodes) is det.
%  Predicate variant: return the current nodes as Nodes.
%  Why: pair with extract//0 for validation in DCG contexts.
extract(Nodes) :-
   extract(Nodes, Nodes).
%! extract// is det.
%  DCG variant: validate that each equivalence class contains its key.
%  Why: ensures that for each class Key-Ids, Key is a member of Ids.
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
