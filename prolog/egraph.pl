:- module(egraph, [add_term//2, add_terms//2, union//2, saturate//1,
                   saturate//2, extract//2, extract_all//2, lookup/2, query//1]).

/** <module> E-graph implementation for term rewriting and saturation

This module implements an E-graph (Equivalence Graph) data structure, 
commonly used for efficient term rewriting, congruence closure, and 
e-matching. The E-graph state is typically threaded through operations 
using DCG notation.

Rewrite rules are automatically compiled into efficient DCG predicates 
via term expansion. See the `egraph_compile` module for full details. 
The supported rule declarations are:
  * egraph:rewrite(Name, Lhs, Rhs)
  * egraph:rewrite(Name, Lhs, Rhs, RhsOptions)
  * egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions)
  * egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions) :- Body
  * egraph:analyze(Name, Lhs, RhsOptions)
  * egraph:analyze(Name, Lhs, LhsOptions, RhsOptions)
  * egraph:analyze(Name, Lhs, LhsOptions, RhsOptions) :- Body
  * egraph:merge_property(Name, V1, V2, Merged)
  * egraph:merge_property(Name, V1, V2, Merged) :- Body
  * egraph:rule(Name, Lhs, Rhs)
  * egraph:rule(Name, Lhs, Rhs) :- Body
  * egraph:rule(Name, Lhs, Rhs, RhsOptions)
  * egraph:rule(Name, Lhs, Rhs, RhsOptions) :- Body
  * egraph:rule(Name, Lhs, LhsOptions, Rhs, RhsOptions)
  * egraph:rule(Name, Lhs, LhsOptions, Rhs, RhsOptions) :- Body

Main predicates:
  * add_term//2: Adds a term to the E-graph, returning its e-class ID.
  * union//2: Merges two e-classes.
  * saturate//1, saturate//2: Applies compiled rewrite rules to the E-graph until saturation or an iteration limit is reached.
  * extract//2: Extracts the optimal term from the E-graph based on term costs.
  * extract_all//2: Extracts all optimal terms from the E-graph based on term costs.
  * lookup/2: Retrieves an e-class node from a sorted list of E-graph nodes.
  * query//1: Queries the E-graph and dynamically binds pattern variables.
*/

:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).
:- use_module(library(heaps)).

:- use_module(egraph/compile).

%!  lookup(+Pair, +SortedPairs) is semidet.
%
%   Retrieves a value from a sorted list of pairs using standard term comparison.
%   The search is unrolled for performance. Adapted from ord_memberchk/2.
%
%   @arg Pair A `Key-Value` pair where `Key` is the target key to find, and `Value` is unified with the associated value.
%   @arg SortedPairs A list of Key-Value pairs sorted by Key.

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

%!  add_term(+Term, -Id)// is det.
%
%   Adds a term to the E-graph, returning its e-class ID.
%   Compound terms are recursively traversed and their arguments 
%   are added to the E-graph first.
%
%   @arg Term The term to be added.
%   @arg Id   The e-class ID representing the added term.

add_term(Term, Node) -->
   add_term(Term, Node, [cost(1)]).
add_term(Var, Id, Opt), var(Var) ==>
   { option(var(What), Opt, node) },
   (  { What == node }
   -> add_node(Var, Id, Opt)
   ;  { What == class }
   -> {  (  option(mark(true), Opt)
         -> put_attr(Id, egraph, true)
         ;  true
         ),
         Var=Id
      }
   ;  { domain_error(node-class, What) }
   ).
add_term('$NODE'(Node), Id, Opt) ==>
   add_node(Node, Id, Opt).
add_term(Term, Id, Opt), is_dict(Term, Tag) ==>
   {
      dict_pairs(Term, Tag, Pairs),
      pairs_keys_values(Pairs, Keys, Values),
      pairs_keys_values(Data, Keys, Ids),
      dict_create(Node, Tag, Data)
   },
   add_terms(Values, Ids, Opt),
   add_node(Node, Id, Opt).
add_term(Term, Id, Opt), compound(Term) ==>
   { Term =.. [F | Args] },
   add_terms(Args, Ids, Opt),
   { Node =.. [F | Ids] },
   add_node(Node, Id, Opt).
add_term(Term, Id, Opt) ==>
   add_node(Term, Id, Opt).

add_terms([], [], _Opt) --> [].
add_terms([Term | Terms], [Id | Ids], Opt) -->
   add_term(Term, Id, Opt),
   add_terms(Terms, Ids, Opt).

add_terms([], _Opt) --> [].
add_terms([Term-Id | Terms], Opt) -->
   add_term(Term, Id, Opt),
   add_terms(Terms, Opt).

add_node(Node-Id, Opt, In, Out) :-
   add_node(Node, Id, Opt, In, Out).
add_node(Node, Id, Opt, In, Out) :-
   (  lookup(Node-node(Id, _Cost), In)
   -> Out = In
   ;  option(nodes(Nodes), Opt), lookup(Node-node(Id, _Cost), Nodes)
   -> Out = In
   ;  (  member(cost(N, Cost), Opt), N == Node
      ;  option(cost(Cost), Opt, 1)
      ),
      !,
      must_be(number, Cost),
      (  option(mark(true), Opt)
      -> put_attr(Id, egraph, true)
      ;  true
      ),
      ord_add_element(In, Node-node(Id, Cost), Out)
   ).

rules([Rule | Rules], M, EGraph, Index, Parents, MinId, UnifsIn, UnifsOut) -->
   { strip_module(M:Rule, Mod, Name) },
   call(Mod:Name, '$empty'-node(_, 0), state([], EGraph, Index, Parents, MinId), UnifsIn, UnifsTmp),
   rules(Rules, M, EGraph, Index, Parents, MinId, UnifsTmp, UnifsOut).
rules([], _, _, _, _, _, Unifs, Unifs) --> [].

make_index(In, Index) :-
   index_pairs(In, UnsortedPairs),
   sort(UnsortedPairs, IdPairs),
   group_pairs_by_key(IdPairs, Groups),
   ord_list_to_rbtree(Groups, Index).

index_pairs([], []).
index_pairs([Node-node(Id, Cost)|T0], [Id-(Node-node(Id, Cost))|T1]) :-
   index_pairs(T0, T1).

make_parents(In, Parents) :-
   phrase(parent_pairs(In), UnsortedPairs),
   sort(UnsortedPairs, IdPairs),
   group_pairs_by_key(IdPairs, Groups),
   ord_list_to_rbtree(Groups, Parents).

parent_pairs([]) ==> [].
parent_pairs([Node-node(Id, Cost) | L]), is_dict(Node) ==>
   { dict_pairs(Node, Tag, Pairs) },
   dict_pairs(Pairs, Node-node(Id, Cost), Tag),
   parent_pairs(L).
parent_pairs([Node-node(Id, Cost) | L]), compound(Node) ==>
   { compound_name_arguments(Node, Name, Args) },
   arg_pairs(Args, Node-node(Id, Cost), Name, _Arity, 0),
   parent_pairs(L).
parent_pairs([_ | L]) ==>
   parent_pairs(L).

dict_pairs([], _, _) --> [].
dict_pairs([_Key-Value | Pairs], Node, Tag) -->
   [Value-Node],
   dict_pairs(Pairs, Node, Tag).

arg_pairs([], _Node, _Name, Arity, Arity) --> [].
arg_pairs([Arg | Args], Node, Name, Arity, I) -->
   [Arg-Node],
   { I1 is I+1 },
   arg_pairs(Args, Node, Name, Arity, I1).

%!  union(+Id1, +Id2)// is det.
%
%   Merges two e-classes by unifying their IDs and merging their underlying nodes.
%
%   @arg Id1 The first e-class ID.
%   @arg Id2 The second e-class ID.

union(A, A) -->
   merge_nodes.

merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   merge_groups(Groups, Tmp, false, Merged),
   (  Merged == true
   -> merge_nodes(Tmp, Out)
   ;  Out = Sort
   ).

merge_groups([Sig-[H | T] | Nodes], [Sig-Node | Worklist], In, Out) :-
   merge_group(T, H, Node),
   (  T == []
   -> Tmp = In
   ;  Tmp = true
   ),
   merge_groups(Nodes, Worklist, Tmp, Out).
merge_groups([], [], In, In).

merge_group([], Node, Node).
merge_group([node(Id, Cost) | T], node(Id, PrevCost), Out) :-
   MinCost is min(Cost, PrevCost),
   (  MinCost < PrevCost
   -> b_setval(egraph_changed, true)
   ;  true
   ),
   merge_group(T, node(Id, MinCost), Out).

apply_unifs([]).
apply_unifs([A=B | L]) :-
   A = B,
   apply_unifs(L).

rebuild(Matches, Unifs, Out) :-
   apply_unifs(Unifs),
   merge_nodes(Matches, Out).

:- meta_predicate saturate(:, ?, ?).
:- meta_predicate saturate(:, +, ?, ?).

%!  saturate(+Rules)// is det.
%
%   Applies a list of compiled rewrite rules to the E-graph until saturation
%   is reached.
%
%   @arg Rules A list of compiled rewrite rule names to apply.

%!  saturate(+Rules, +N)// is det.
%
%   Applies a list of compiled rewrite rules to the E-graph up to N times
%   or until saturation is reached.
%
%   @arg Rules A list of compiled rewrite rule names to apply.
%   @arg N     The maximum number of iterations (or `inf` for no limit).

saturate(M:Rules) -->
   saturate(M:Rules, inf).
saturate(M:Rules, N, In, Out) :-
   (  N > 0
   -> b_setval(egraph_changed, false),
      run_rules(Rules, M, In, Matches, In, Unifs),
      rebuild(Matches, Unifs, Tmp),
      length(In, Len1),
      length(Tmp, Len2),
      b_getval(egraph_changed, Changed),
      debug(saturate, "~p", [Len1-Len2-Changed]),
      (  (Len1 \== Len2 ; Changed == true)
      -> (  N == inf
         -> N1 = N
         ;  N1 is N - 1
         ),
         saturate(M:Rules, N1, Tmp, Out)
      ;  Out = Tmp
      )
   ;  Out = In
   ).

run_rules(Rules, M, In, Matches, Tail, Unifs) :-
   make_index(In, Index),
   make_parents(In, Parents),
   (  rb_min(Index, MinId, _) -> true ; MinId = 0 ),
   phrase(rules(Rules, M, In, Index, Parents, MinId, Unifs, []), Matches, Tail).

%!  query(?Pattern)// is multi.
%
%   Queries the E-graph and dynamically binds pattern variables.
%   Upon success, the variables in the query are bound and the `Pattern`
%   is unified with the complete extracted matching term from the E-graph.
%   On backtracking, `Pattern` will be bound to all possible representations
%   of the matched equivalence class in increasing order of cost.
%
%   @arg Pattern The term pattern to search for, which is unified with the fully extracted match.

query(Pattern, In, Out) :-
   copy_term(Pattern, PatternCopy),
   variant_sha1(PatternCopy, Sha),
   atom_concat('query_', Sha, RuleName),
   (  current_predicate(RuleName/_)
   -> true
   ;  quote_vars(PatternCopy, QuotedPat),
      Rule = rule(RuleName, [QuotedPat-Id], [], [query(Id)-_], []),
      phrase(egraph_compile:compile(Rule :- true), Clauses),
      maplist(maplist(assert_ssu), Clauses)
   ),
   run_rules([RuleName], egraph, In, Matches, [], _Unifs),
   pairs_keys(Matches, Queries),
   sort(Queries, SortedQueries),
   member(query(MatchId), SortedQueries),
   extract_all(MatchId, Pattern, In, Out).

assert_ssu((Head, Guard) => Body) =>
   assertz(?=>(Head, (Guard, !, Body))).
assert_ssu(Head => Body) =>
   assertz(Head => Body).
assert_ssu(_) => true.

quote_vars(Var, '$NODE'(Var)) :- var(Var), !.
quote_vars(Dict, Quoted) :- is_dict(Dict), !,
   dict_pairs(Dict, Tag, Pairs),
   maplist(quote_pair, Pairs, QuotedPairs),
   dict_pairs(Quoted, Tag, QuotedPairs).
quote_vars(Compound, Quoted) :- compound(Compound), !,
   compound_name_arguments(Compound, Name, Args),
   maplist(quote_vars, Args, QuotedArgs),
   compound_name_arguments(Quoted, Name, QuotedArgs).
quote_vars(Atomic, Atomic).

quote_pair(K-V, K-QV) :- quote_vars(V, QV).

%!  extract(Id, Extracted)// is det.
%
%   Extracts the optimal term from the E-graph based on term costs.
%
%   @arg Id The eclass Id to be extracted as returned by add_term
%   @arg Extracted the extracted term

extract(Target, Extracted, EGraph, EGraph) :-
   current_prolog_flag(float_overflow, Flag),
   setup_call_cleanup(
      set_prolog_flag(float_overflow, infinity),
      (  dijkstra(Target, EGraph, Costs),
         extract_class(Costs, Target, Extracted)
      ),
      set_prolog_flag(float_overflow, Flag)
   ).
extract_class(Costs, Target, Extracted) :-
   rb_lookup(Target, _-Node, Costs),
   extract_node(Costs, Node, Extracted).
extract_node(Costs, Dict, R), is_dict(Dict) =>
   dict_pairs(Dict, Tag, Pairs),
   pairs_keys_values(Pairs, Keys, Classes),
   pairs_keys_values(NewPairs, Keys, Values),
   dict_pairs(R, Tag, NewPairs),
   maplist(extract_class(Costs), Classes, Values).
extract_node(Costs, Compound, R), compound(Compound) =>
   compound_name_arguments(Compound, Name, Classes),
   same_length(Classes, Values),
   compound_name_arguments(R, Name, Values),
   maplist(extract_class(Costs), Classes, Values).
extract_node(_, Atomic, R) =>
   R = Atomic.

dijkstra(Target, EGraph, CostsOut) :-
   empty_heap(HeapIn),
   rb_new(EmptyCosts),
   setup(EGraph, ParentPairs, EmptyCosts, CostsIn, HeapIn, HeapOut),
   keysort(ParentPairs, SortedParentPairs),
   group_pairs_by_key(SortedParentPairs, GroupedParentPairs),
   ord_list_to_rbtree(GroupedParentPairs, Parents),
   dijkstra(Target, Parents, HeapOut, CostsIn, CostsOut).
dijkstra(Target, Parents, HeapIn, CostsIn, CostsOut) :-
   (  get_from_heap(HeapIn, CurrentCost, Class, HeapTmp)
   -> (  Class == Target
      -> CostsOut = CostsIn
      ;  rb_lookup(Class, ClassCost-_, CostsIn),
         (  CurrentCost > ClassCost
         -> dijkstra(Target, Parents, HeapTmp, CostsIn, CostsOut)
         ;  (  rb_lookup(Class, ClassParents, Parents)
            -> true
            ;  ClassParents = []
            ),
            update_parents(ClassParents, CostsIn, CostsTmp, HeapTmp, HeapOut),
            dijkstra(Target, Parents, HeapOut, CostsTmp, CostsOut)
         )
      )
   ;  CostsOut = CostsIn
   ).
update_parents([], Costs, Costs, Heap, Heap).
update_parents([ParentNode-node(ParentClass, ParentCost) | Parents], CostsIn, CostsOut, HeapIn, HeapOut) :-
   (  is_dict(ParentNode)
   -> dict_pairs(ParentNode, _, KeysValues),
      pairs_values(KeysValues, ChildClasses)
   ;  compound(ParentNode)
   -> compound_name_arguments(ParentNode, _, ChildClasses)
   ;  ChildClasses = []
   ),
   compute_cost(ChildClasses, CostsIn, ParentCost, Cost),
   (  rb_lookup(ParentClass, CurrentCost-_, CostsIn)
   -> true
   ;  CurrentCost = inf
   ),
   (  Cost < CurrentCost
   -> rb_insert(CostsIn, ParentClass, Cost-ParentNode, CostsTmp),
      add_to_heap(HeapIn, Cost, ParentClass, HeapTmp)
   ;  CostsTmp = CostsIn, HeapTmp = HeapIn
   ),
   update_parents(Parents, CostsTmp, CostsOut, HeapTmp, HeapOut).

   
compute_cost([], _, Cost, Cost).
compute_cost([Child | Childs], Costs, CostIn, CostOut) :-
   (  rb_lookup(Child, ChildCost-_, Costs)
   -> true
   ;  ChildCost = inf
   ),
   CostTmp is CostIn + ChildCost,
   compute_cost(Childs, Costs, CostTmp, CostOut).

setup([], [], Cost, Cost, Heap, Heap).
setup([Node-node(ClassId, NodeCost) | Nodes], ParentsIn, CostIn, CostOut, HeapIn, HeapOut) :-
   (  is_dict(Node)
   -> dict_pairs(Node, _, KeysValues),
      pairs_values(KeysValues, ChildClasses)
   ;  compound(Node)
   -> compound_name_arguments(Node, _, ChildClasses)
   ;  ChildClasses = []
   ),
   (  ChildClasses == []
   -> ParentsOut = ParentsIn,
      (  (rb_lookup(ClassId, CurCost-_, CostIn) ; CurCost = inf), NodeCost < CurCost
      -> rb_insert(CostIn, ClassId, NodeCost-Node, CostTmp),
         add_to_heap(HeapIn, NodeCost, ClassId, HeapTmp)
      ;  CostTmp = CostIn, HeapTmp = HeapIn
      )
   ;  insert_parent(ChildClasses, Node-node(ClassId, NodeCost), ParentsIn, ParentsOut),
      CostTmp = CostIn, HeapTmp = HeapIn
   ),
   setup(Nodes, ParentsOut, CostTmp, CostOut, HeapTmp, HeapOut).

insert_parent([], _, Parents, Parents).
insert_parent([ChildClass | ChildClasses], Node, [ChildClass-Node | ParentsTmp], ParentsOut) :-
   insert_parent(ChildClasses, Node, ParentsTmp, ParentsOut).

extract_all(Target, Extracted, EGraph, EGraph) :-
   current_prolog_flag(float_overflow, Flag),
   setup_call_cleanup(
      set_prolog_flag(float_overflow, infinity),
      (  dijkstra(_, EGraph, Costs),
         extract_all_(EGraph, Costs, Target, Extracted)
      ),
      set_prolog_flag(float_overflow, Flag)
   ).

extract_all_index(EGraph, Index) :-
   extract_pairs(EGraph, UnsortedPairs),
   keysort(UnsortedPairs, IdPairs),
   group_pairs_by_key(IdPairs, Groups),
   ord_list_to_rbtree(Groups, Index).

extract_pairs([], []).
extract_pairs([Node-node(Id, Cost)|T0], [Id-(Node-Cost)|T1]) :-
   extract_pairs(T0, T1).

extract_all_(Egraph, Costs, Target, Extracted) :-
   empty_heap(HeapIn),
   rb_lookup(Target, H-_, Costs),
   State = state(0, [], [Target]),
   add_to_heap(HeapIn, H, State, HeapOut),
   extract_all_index(Egraph, Index),
   extract_all__(Index, Costs, HeapOut, Unifs),
   reverse(Unifs, PreOrder),
   build_term(PreOrder, [], Extracted).

build_term([_-Value | UnifsIn], UnifsOut, Term) :-
   (  var(Value)
   -> Term = Value,
      UnifsOut = UnifsIn
   ;  is_dict(Value)
   -> dict_pairs(Value, Tag, Pairs),
      pairs_keys_values(Pairs, Keys, ChildClasses),
      build_terms(ChildClasses, UnifsIn, UnifsOut, Values),
      pairs_keys_values(NewPairs, Keys, Values),
      dict_pairs(Term, Tag, NewPairs)
   ;  compound(Value)
   -> compound_name_arguments(Value, Name, ChildClasses),
      build_terms(ChildClasses, UnifsIn, UnifsOut, Values),
      compound_name_arguments(Term, Name, Values)
   ;  Term = Value,
      UnifsOut = UnifsIn
   ).

build_terms([], Unifs, Unifs, []).
build_terms([_|Cs], UnifsIn, UnifsOut, [V|Vs]) :-
   build_term(UnifsIn, UnifsTmp, V),
   build_terms(Cs, UnifsTmp, UnifsOut, Vs).

extract_all__(Index, Costs, HeapIn, Unifs) :-
   (  get_from_heap(HeapIn, _, state(G, PartialTerm, PendingHoles), HeapTmp)
   -> (  PendingHoles == []
      -> (  Unifs = PartialTerm
         ;  extract_all__(Index, Costs, HeapTmp, Unifs)
         )
      ;  [Hole | RestHoles] = PendingHoles,
         rb_lookup(Hole, Nodes, Index),
         extract_all_childs(Nodes, Costs, G, PartialTerm, Hole, RestHoles, HeapTmp, HeapOut),
         extract_all__(Index, Costs, HeapOut, Unifs)
      )
   ).

extract_all_childs([], _, _, _, _, _, Heap, Heap).
extract_all_childs([Node-NodeCost | Nodes], Costs, G, PartialTerm, Hole, RestHoles, HeapIn, HeapOut) :-
   (  is_dict(Node)
   -> dict_pairs(Node, _, KeysValues),
      pairs_values(KeysValues, ChildClasses)
   ;  compound(Node)
   -> compound_name_arguments(Node, _, ChildClasses)
   ;  ChildClasses = []
   ),
   NewPartialTerm = [Hole-Node | PartialTerm],
   append(ChildClasses, RestHoles, NewHoles),

   NewG is G + NodeCost,
   foldl(sum_costs(Costs), NewHoles, 0, H),
   F is NewG + H,
   add_to_heap(HeapIn, F, state(G, NewPartialTerm, NewHoles), HeapTmp),
   extract_all_childs(Nodes, Costs, G, PartialTerm, Hole, RestHoles, HeapTmp, HeapOut).

sum_costs(Costs, Hole, In, Out) :-
   rb_lookup(Hole, Cost-_, Costs),
   Out is In + Cost.

:- begin_tests(egraph_add_terms).

test_term(Var, [Var-node(_, 1)]).
test_term('$NODE'(Var), [Var-node(_, 1)]).
test_term(tag{k1: v1, k2: v2}, [v1-node(I1, 1), v2-node(I2, 1), tag{k1: I1, k2: I2}-node(_, 1)]).
test_term(f(arg1, arg2), [arg1-node(I1, 1), arg2-node(I2, 1), f(I1, I2)-node(_, 1)]).
test_term(simple_atom, [simple_atom-node(_, 1)]).

test(add_term, [forall(test_term(Term, Expected)), OutNodes =@= Expected]) :-
   phrase(add_term(Term, _Id, [var(node)]), [], OutNodes).

:- end_tests(egraph_add_terms).
