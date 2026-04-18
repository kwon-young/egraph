:- module(egraph, [add_term//2, union//2, saturate//1, saturate//2,
                   extract//2, lookup/2]).

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

Main predicates:
  * add_term//2: Adds a term to the E-graph, returning its e-class ID.
  * union//2: Merges two e-classes.
  * saturate//1, saturate//2: Applies compiled rewrite rules to the E-graph until saturation or an iteration limit is reached.
  * extract//2: Extracts the optimal term from the E-graph based on term costs.
  * lookup/2: Retrieves an e-class node from a sorted list of E-graph nodes.
*/

:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).
:- use_module(library(heaps)).

:- use_module(egraph/compile).

cost:attr_unify_hook(_, _) :-
   true.
const:attr_unify_hook(XConst, Y) :-
   (  get_attr(Y, const, YConst)
   -> (  XConst =:= YConst
      -> true
      ;  domain_error(XConst, YConst)
      )
   ;  var(Y)
   -> put_attr(Y, const, XConst)
   ;  true
   ).

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
%   are added to the E-graph first. Variables are represented using 
%   '$VAR'/1 wrappers.
%
%   @arg Term The term to be added.
%   @arg Id   The e-class ID representing the added term.

add_term(Term, Id), var(Term) ==>
   add_node('$VAR'(Term), Id).
add_term(Term, Id), is_dict(Term) ==>
   % rework this with dict_same_keys
   {
      dict_pairs(Term, Tag, Pairs),
      pairs_keys_values(Pairs, Keys, Values)
   },
   foldl(add_term, Values, Ids),
   {
      pairs_keys_values(Data, Keys, Ids),
      dict_create(Node, Tag, Data)
   },
   add_node(Node, Id).
add_term(Term, Id), compound(Term) ==>
   { Term =.. [F | Args] },
   foldl(add_term, Args, Ids),
   { Node =.. [F | Ids] },
   add_node(Node, Id).
add_term(Term, Id) ==>
   add_node(Term, Id).

add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-node(Id, _Cost), In)
   -> Out = In
   ;  ord_add_element(In, Node-node(Id, 1), Out),
      (  number(Node)
      -> put_attr(Id, const, Node)
      ;  true
      )
   ).

% rules([Rule | Rules], Index, Pat-node(Id, Cost), UnifsIn, UnifsOut) -->
%    call(Rule, Pat, Id, Index, UnifsIn, UnifsTmp),
%    rules(Rules, Index, Pat-node(Id, Cost), UnifsTmp, UnifsOut).
% rules([], _, _, Unifs, Unifs) --> [].

:- dynamic rules//5.
:- non_terminal(user:egraph:rules/7).

chain_rule(M, Pat, Id, Index, Rule, Mod:Call, UnifsIn, UnifsOut) :-
   strip_module(M:Rule, Mod, Name),
   Call =.. [Name, Pat, Id, Index, UnifsIn, UnifsOut].

:- meta_predicate compile_rules(:, -).

compile_rules(M:Rules, RulesId) :-
   term_hash(M:Rules, RulesId),
   (  clause(rules(RulesId, _, _, _, _, _, _), _)
   -> true
   ;  (  Rules = [_ | _]
      -> foldl(chain_rule(M, Pat, Id, Index), Rules, Calls, UnifsIn, UnifsOut),
         comma_list(Body, Calls)
      ;  Body = true, UnifsOut = UnifsIn
      ),
      Head = egraph:rules(RulesId, Index, Pat-node(Id, _), UnifsIn, UnifsOut),
      Clause = (Head --> Body),
      expand_term(Clause, Term),
      asserta(Term)
   ).


make_index(In, Index) :-
   index_pairs(In, UnsortedPairs),
   keysort(UnsortedPairs, IdPairs),
   group_pairs_by_key(IdPairs, Groups),
   ord_list_to_rbtree(Groups, Index).

index_pairs([], []).
index_pairs([Node-node(Id, _Cost)|T0], [Id-Node|T1]) :-
   index_pairs(T0, T1).

match([], _, _, Unifs, Unifs) --> [].
match([Node | Rest], Rules, Index, UnifsIn, UnifsOut) -->
   rules(Rules, Index, Node, UnifsIn, UnifsTmp),
   match(Rest, Rules, Index, UnifsTmp, UnifsOut).

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
   merge_group(T, node(Id, MinCost), Out).

apply_unifs([]).
apply_unifs([A=A | L]) :-
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

saturate(M:Rules) -->
   saturate(M:Rules, inf).

%!  saturate(+Rules, +N)// is det.
%
%   Applies a list of compiled rewrite rules to the E-graph up to N times
%   or until saturation is reached.
%
%   @arg Rules A list of compiled rewrite rule names to apply.
%   @arg N     The maximum number of iterations (or `inf` for no limit).

saturate(M:Rules, N) -->
   { compile_rules(M:Rules, RulesId) },
   saturate_(RulesId, N).

saturate_(Rules, N, In, Out) :-
   (  N > 0
   -> make_index(In, Index),
      match(In, Rules, Index, Unifs, [], Matches, In),
      rebuild(Matches, Unifs, Tmp),
      length(In, Len1),
      length(Tmp, Len2),
      (  Len1 \== Len2
      -> (  N == inf
         -> N1 = N
         ;  N1 is N - 1
         ),
         saturate_(Rules, N1, Tmp, Out)
      ;  Out = Tmp
      )
   ;  Out = In
   ).

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
extract_node(_, '$VAR'(Var), R) =>
   R = Var.
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
   ;  compound(ParentNode), ParentNode \= '$VAR'(_)
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
   ;  compound(Node), Node \= '$VAR'(_)
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
