:- module(egraph, [add//2, union//2, saturate//1, saturate//2,
                   extract/1, extract//0]).

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

add(Term, Id, In, Out) :-
   (  compound(Term)
   -> Term =.. [F | Args],
      foldl(add, Args, Ids, In, Tmp),
      Node =.. [F | Ids],
      add_node(Node, Id, Tmp, Out)
   ;  add_node(Term, Id, In, Out)
   ).

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

comm((A+B)-AB, _Nodes, UnifsIn, UnifsOut) ==>
   { UnifsOut = [AB=BA | UnifsIn] },
   [B+A-BA].
comm((A*B)-AB, _Nodes, UnifsIn, UnifsOut) ==>
   { UnifsOut = [AB=BA | UnifsIn] },
   [B*A-BA].
comm(_, _, Unifs, Unifs) ==> [].

assoc((A+BC)-ABC, Index, UnifsIn, UnifsOut) ==>
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, +, A, ABC, UnifsIn, UnifsOut).
assoc((A*BC)-ABC, Index, UnifsIn, UnifsOut) ==>
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, *, A, ABC, UnifsIn, UnifsOut).
assoc(_, _, Unifs, Unifs) ==> [].
assoc_([(B+C) | Nodes], +, A, ABC, UnifsIn, UnifsOut) ==>
   {  put_attr(AB, cost, [A+B]),
      put_attr(ABC_, cost, [AB+C]),
      UnifsTmp = [ABC=ABC_ | UnifsIn]
   },
   [A+B-AB, AB+C-ABC_],
   assoc_(Nodes, +, A, ABC, UnifsTmp, UnifsOut).
assoc_([(B*C) | Nodes], *, A, ABC, UnifsIn, UnifsOut) ==>
   {  put_attr(AB, cost, [A*B]),
      put_attr(ABC_, cost, [AB*C]),
      UnifsTmp = [ABC=ABC_ | UnifsIn]
   },
   [A*B-AB, AB+C-ABC_],
   assoc_(Nodes, *, A, ABC, UnifsTmp, UnifsOut).
assoc_([_ | Nodes], Op, A, ABC, UnifsIn, UnifsOut) ==>
   assoc_(Nodes, Op, A, ABC, UnifsIn, UnifsOut).
assoc_([], _, _, _, Unifs, Unifs) ==> [].

reduce(A+B-AB, _Index, UnifsIn, UnifsOut), get_attr(B, const, 0) ==>
   { UnifsOut = [A=AB | UnifsIn] },
   [].
reduce(A*B-AB, _Index, UnifsIn, UnifsOut), get_attr(B, const, 1) ==>
   { UnifsOut = [A=AB | UnifsIn] },
   [].
reduce(_*B-AB, _Index, UnifsIn, UnifsOut), get_attr(B, const, 0) ==>
   { UnifsOut = [B=AB | UnifsIn] },
   [].
reduce(_, _, Unifs, Unifs) ==> [].

factorize(A+A-AA, _Index, UnifsIn, UnifsOut) ==>
   {  put_attr(Two, const, 2),
      put_attr(Two, cost, [0.9]),
      put_attr(A2, cost, [A*Two]),
      UnifsOut = [A2=AA | UnifsIn]
   },
   [2-Two, A*Two-A2].
factorize(A+BA-AA, Index, UnifsIn, UnifsOut) ==>
   { rb_lookup(BA, Nodes, Index) },
   factorize(Nodes, A, AA, UnifsIn, UnifsOut).
factorize(_, _, Unifs, Unifs) ==> [].
factorize([B*A | Nodes], A, AA, UnifsIn, UnifsOut) ==>
   {  put_attr(One, const, 1),
      put_attr(One, cost, [0.9]),
      put_attr(B1, cost, [B+One]),
      put_attr(B1A, cost, [B1*A]),
      UnifsTmp = [B1A=AA | UnifsIn]
   },
   [1-One, B+One-B1, B1*A-B1A],
   factorize(Nodes, A, AA, UnifsTmp, UnifsOut).
factorize([_ | Nodes], A, AA, UnifsIn, UnifsOut) ==>
   factorize(Nodes, A, AA, UnifsIn, UnifsOut).
factorize([], _, _, Unifs, Unifs) ==> [].

constant_folding((A+B)-AB, _Index, UnifsIn, UnifsOut),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA+VB,
      put_attr(C, const, VC),
      put_attr(C, cost, [1]),
      UnifsOut = [C=AB | UnifsIn]
   },
   [VC-C].
constant_folding((A*B)-AB, _Index, UnifsIn, UnifsOut),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA*VB,
      put_attr(C, const, VC),
      put_attr(C, cost, [1]),
      UnifsOut = [C=AB | UnifsIn]
   },
   [VC-C].
constant_folding(_, _, Unifs, Unifs) ==> [].

rules([Rule | Rules], Index, Node, UnifsIn, UnifsOut) -->
   call(Rule, Index, Node, Rule, UnifsIn, Unifs),
   rules(Rules, Index, Node, Unifs, UnifsOut).
rules([], _, _, Unifs, Unifs) --> [].
% rules(Rules, Index, Node) -->
%    sequence(rule(Index, Node), Rules).
% rule(Index, Node, Rule) -->
%    call(Rule, Node, Index).

make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

match(Rules, Worklist, Index, Matches, Unifs) :-
   foldl(rules(Rules, Index), Worklist, Unifs, [], Matches, []).

union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   merge_group(Groups, Tmp, false, Merged),
   (  Merged == true
   -> merge_nodes(Tmp, Out)
   ;  Out = Sort
   ).

merge_group([Node-[H | T] | Nodes], [Node-H | Worklist], In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Tmp = In
   ;  Tmp = true
   ),
   merge_group(Nodes, Worklist, Tmp, Out).
merge_group([], [], In, In).

% rebuild([A=B | T], In, Out) :-
%    A = B,
%    rebuild(T, In, Out).
% rebuild([N-Id | T], In, Out) :-
%    rebuild(T, [N-Id | In], Out).
% rebuild([], In, Out) :-
%    merge_nodes(In, Out).
rebuild(Matches, Unifs, In, Out) :-
   maplist(call, Unifs),
   append(Matches, In, Tmp),
   merge_nodes(Tmp, Out).
              
saturate(Rules) -->
   saturate(Rules, inf).
saturate(Rules, N, In, Out) :-
   (  N > 0
   -> make_index(In, Index),
      match(Rules, In, Index, Matches, Unifs),
      rebuild(Matches, Unifs, In, Tmp),
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
   maplist([Node-NodeId, (Cost-Node)-NodeId]>>(merge_cost(Node, Cost) -> true ; Cost = inf),
           Nodes, CostNodes),
   make_index(CostNodes, Index),
   rb_visit(Index, Pairs),
   maplist([NodeId-SubCostNodes]>>(
      keysort(SubCostNodes, Sort),
      member(Cost-NodeId, Sort)
   ), Pairs).
:- table get_cost/2.
get_cost(Id, Cost) :-
   get_attr(Id, cost, Costs),
   foldl(merge_cost, Costs, inf, Cost).
merge_cost(Node, Cost) :-
   (  compound(Node)
   -> merge_cost(Node, inf, Cost)
   ;  Cost = 1
   ).
:- table merge_cost/3.
merge_cost(Cost, In, Out) :-
   (  compound(Cost)
   -> Cost =.. [_ | Ids],
      maplist(get_cost, Ids, Costs),
      sum_list([1 | Costs], RealCost)
   ;  RealCost = Cost
   ),
   Out is min(In, RealCost).

example1(G) :-
   phrase((
      add(a, A),
      add(f(f(a)), FFA),
      union(A, FFA),
      add(f(f(f(f(a)))), _FFFFA)
   ), [], G).


add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add(Expr, _), [], G),
   time(saturate([comm, assoc], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

example3(N, Expr, T) :-
   distinct(R, phrase((
      add(Expr, R),
      saturate([comm, assoc, reduce, constant_folding], N),
      extract(R, T)
   ), [], _)).
