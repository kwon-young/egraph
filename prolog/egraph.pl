:- module(egraph, [add_term//2, union//2, saturate//1, saturate//2,
                   extract/1, extract//0, lookup/2]).

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
  * extract/1, extract//0: Extracts the optimal term(s) from the E-graph based on term costs.
  * lookup/2: Retrieves an e-class node from a sorted list of E-graph nodes.
*/

:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).
:- use_module(library(clpr)).

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

rules([Rule | Rules], Index, Pat-node(Id, Cost), UnifsIn, UnifsOut) -->
   call(Rule, Pat, Id, Index, UnifsIn, UnifsTmp),
   rules(Rules, Index, Pat-node(Id, Cost), UnifsTmp, UnifsOut).
rules([], _, _, Unifs, Unifs) --> [].

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
              
%!  saturate(+Rules)// is det.
%
%   Applies a list of compiled rewrite rules to the E-graph until saturation
%   is reached.
%
%   @arg Rules A list of compiled rewrite rule names to apply.

saturate(Rules) -->
   saturate(Rules, inf).

%!  saturate(+Rules, +N)// is det.
%
%   Applies a list of compiled rewrite rules to the E-graph up to N times
%   or until saturation is reached.
%
%   @arg Rules A list of compiled rewrite rule names to apply.
%   @arg N     The maximum number of iterations (or `inf` for no limit).

saturate(Rules, N, In, Out) :-
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
         saturate(Rules, N1, Tmp, Out)
      ;  Out = Tmp
      )
   ;  Out = In
   ).

%!  extract(+Nodes) is det.
%!  extract// is det.
%
%   Extracts the optimal term(s) from the E-graph based on term costs.
%
%   @arg Nodes A list of E-graph nodes representing the state.

extract(Nodes) :-
   extract(Nodes, Nodes).
extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   maplist([node(Id, Cost)-Node, Id-node(Cost, Node)]>>true, Pairs, IdPairs),
   group_pairs_by_key(IdPairs, ClassNodes),
   maplist([Id-_Node]>>({Cost >= 0}, put_attr(Id, cost, Cost)), ClassNodes),
   maplist(compute_class_cost, ClassNodes, NewClassNodes),
   maplist(extract_class, NewClassNodes).

extract_class(Id-Nodes) :-
   % make sure that costs are instantiated
   sort(Nodes, SortedNodes),
   member(node(_Cost, Node), SortedNodes),
   (  Node = '$VAR'(Var)
   -> Id = Var
   ;  Id = Node
   ),
   (  var(Id)
   -> del_attr(Id, cost)
   ;  true
   ).

compute_class_cost(Id-Nodes, Id-NewNodes) :-
   maplist(compute_node_cost, Nodes, NewNodes, NodeCosts),
   NodeCosts = [FirstCost | RestCosts],
   foldl([NodeCost, Cost, MinCost]>>
         {MinCost = min(NodeCost, Cost)},
         RestCosts, FirstCost, ClassCost),
   get_attr(Id, cost, ClassCost).
compute_node_cost(node(Offset, Node), node(Cost, Node), Cost) :-
   (  Node = '$VAR'(_)
   -> Cost = Offset
   ;  compound(Node)
   -> Node =.. [_ | Ids],
      foldl([Id, In, Out]>>(
         get_attr(Id, cost, IdCost),
         {Out = In + IdCost}
      ), Ids, 0, CCost),
      { Cost = CCost + Offset }
   ;  Cost = Offset
   ).
