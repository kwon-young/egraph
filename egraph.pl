:- module(egraph, [add_term//2, union//2, saturate//1, saturate//2,
                   extract/1, extract//0, lookup/2]).

:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).
:- use_module(library(clpBNR)).

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

add_term(Term, Id, In, Out) :-
   (  compound(Term)
   -> Term =.. [F | Args],
      foldl(add_term, Args, Ids, In, Tmp),
      Node =.. [F | Ids],
      add_node(Node, Id, Tmp, Out)
   ;  add_node(Term, Id, In, Out)
   ).

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

comm(A+B, AB, _Index, UnifsIn, UnifsOut) ==>
   { UnifsIn = [AB=BA | UnifsOut] },
   [B+A-node(BA, 1)].
comm(_, _, _, UnifsIn, UnifsOut) ==> {UnifsOut = UnifsIn}.

assoc(A+BC, ABC, Index, UnifsIn, UnifsOut) ==>
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A+BC, ABC, UnifsIn, UnifsOut).
assoc(_, _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.
assoc_([Node | Nodes], Pat, Top, UnifsIn, UnifsOut) ==>
   assoc__(Node, Pat, Top, UnifsIn, UnifsTmp),
   assoc_(Nodes, Pat, Top, UnifsTmp, UnifsOut).
assoc_([], _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.
assoc__(B+C, A+_BC, ABC, UnifsIn, UnifsOut) ==>
   { UnifsIn = [ABC=ABC_ | UnifsOut] },
   [A+B-node(AB, 1), AB+C-node(ABC_, 1)].
assoc__(_, _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

reduce(A+B, AB, _Index, UnifsIn, UnifsOut), get_attr(B, const, 0) ==>
   { UnifsIn = [A=AB | UnifsOut] },
   [].
reduce(A*B, AB, _Index, UnifsIn, UnifsOut), get_attr(B, const, 1) ==>
   { UnifsIn = [A=AB | UnifsOut] },
   [].
reduce(_*B, AB, _Index, UnifsIn, UnifsOut), get_attr(B, const, 0) ==>
   { UnifsIn = [B=AB | UnifsOut] },
   [].
reduce(_, _, _, UnifsIn, UnifsOut) ==> {UnifsOut = UnifsIn}.

factorize1(A+A, AA, _Index, UnifsIn, UnifsOut) ==>
   {  put_attr(Two, const, 2),
      UnifsIn = [A2=AA | UnifsOut]
   },
   % make sure to use rationals for fractional costs
   % so that clpBNR cost variables always bounds to concrete values
   [2-node(Two, 1), A*Two-node(A2, 9r10)].
factorize1(_, _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

factorize2(A+BA, AA, Index, UnifsIn, UnifsOut) ==>
   { rb_lookup(BA, Nodes, Index) },
   factorize2_(Nodes, A, AA, UnifsIn, UnifsOut).
factorize2(_, _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

factorize2_([B*A | Nodes], A, AA, UnifsIn, UnifsOut) ==>
   {  put_attr(One, const, 1),
      UnifsIn = [B1A=AA | UnifsTmp]
   },
   [1-node(One, 1), B+One-node(B1, 1), B1*A-node(B1A, 9r10)],
   factorize2_(Nodes, A, AA, UnifsTmp, UnifsOut).
factorize2_([_ | Nodes], A, AA, UnifsIn, UnifsOut) ==>
   factorize2_(Nodes, A, AA, UnifsIn, UnifsOut).
factorize2_([], _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

constant_folding(A+B, AB, _Index, UnifsIn, UnifsOut),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA+VB,
      put_attr(C, const, VC),
      UnifsIn = [C=AB | UnifsOut]
   },
   [VC-node(C, 1)].
constant_folding(A*B, AB, _Index, UnifsIn, UnifsOut),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA*VB,
      put_attr(C, const, VC),
      UnifsIn = [C=AB | UnifsOut]
   },
   [VC-node(C, 1)].
constant_folding(_, _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

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

union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

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
              
saturate(Rules) -->
   saturate(Rules, inf).
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
   member(node(_Cost, Id), SortedNodes),
   (  var(Id)
   -> del_attr(Id, cost)
   ;  true
   ).

compute_class_cost(Id-Nodes, Id-NewNodes) :-
   maplist(compute_node_cost, Nodes, NewNodes, NodeCosts),
   foldl([NodeCost, Cost, MinCost]>>
         {MinCost is min(NodeCost, Cost)},
         NodeCosts, inf, ClassCost),
   get_attr(Id, cost, ClassCost).
compute_node_cost(node(Offset, Node), node(Cost, Node), Cost) :-
   (  compound(Node)
   -> Node =.. [_ | Ids],
      foldl([Id, In, Out]>>(
         get_attr(Id, cost, IdCost),
         {Out is In + IdCost}
      ), Ids, 0, CCost),
      { Cost is CCost + Offset }
   ;  Cost = Offset
   ).

example1(G) :-
   phrase((
      add_term(a, A),
      add_term(f(f(a)), FFA),
      union(A, FFA),
      add_term(f(f(f(f(a)))), _FFFFA)
   ), [], G).


add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add_term(Expr, _), [], G),
   time(saturate([comm, assoc], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

example3(N, Expr, R) :-
   distinct(R, phrase((
      add_term(Expr, R),
      saturate([comm, assoc, factorize1, factorize2, constant_folding], N),
      saturate([reduce], N), % reduce with comm+assoc+factorize explodes
      extract
   ), [], _)).
