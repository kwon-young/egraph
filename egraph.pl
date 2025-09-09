:- module(egraph, [add_term//2, union//2, saturate//1, saturate//2,
                   extract/1, extract//0]).

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

comm((A+B)-node(AB, ABCost), _Index, UnifsIn, UnifsOut) ==>
   { UnifsIn = [AB=BA | UnifsOut] },
   [B+A-node(BA, ABCost)].
comm((A*B)-node(AB, ABCost), _Index, UnifsIn, UnifsOut) ==>
   { UnifsIn = [AB=BA | UnifsOut] },
   [B*A-node(BA, ABCost)].
comm(_, _, UnifsIn, UnifsOut) ==> {UnifsOut = UnifsIn}.

assoc((A+BC)-ABC, Index, UnifsIn, UnifsOut) ==>
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, +, A, ABC, UnifsIn, UnifsOut).
assoc((A*BC)-ABC, Index, UnifsIn, UnifsOut) ==>
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, *, A, ABC, UnifsIn, UnifsOut).
assoc(_, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.
assoc_([(B+C) | Nodes], +, A, node(ABC, ABCCost), UnifsIn, UnifsOut) ==>
   { UnifsIn = [ABC=ABC_ | UnifsTmp] },
   [A+B-node(AB, 1), AB+C-node(ABC_, ABCCost)],
   assoc_(Nodes, +, A, node(ABC, ABCCost), UnifsTmp, UnifsOut).
assoc_([(B*C) | Nodes], *, A, node(ABC, ABCCost), UnifsIn, UnifsOut) ==>
   { UnifsIn = [ABC=ABC_ | UnifsTmp] },
   [A*B-node(AB, 1), AB*C-node(ABC_, ABCCost)],
   assoc_(Nodes, *, A, node(ABC, ABCCost), UnifsTmp, UnifsOut).
assoc_([_ | Nodes], Op, A, ABC, UnifsIn, UnifsOut) ==>
   assoc_(Nodes, Op, A, ABC, UnifsIn, UnifsOut).
assoc_([], _, _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

reduce(A+B-node(AB, _), _Index, UnifsIn, UnifsOut), get_attr(B, const, 0) ==>
   { UnifsIn = [A=AB | UnifsOut] },
   [].
reduce(A*B-node(AB, _), _Index, UnifsIn, UnifsOut), get_attr(B, const, 1) ==>
   { UnifsIn = [A=AB | UnifsOut] },
   [].
reduce(_*B-node(AB, _), _Index, UnifsIn, UnifsOut), get_attr(B, const, 0) ==>
   { UnifsIn = [B=AB | UnifsOut] },
   [].
reduce(_, _, UnifsIn, UnifsOut) ==> {UnifsOut = UnifsIn}.

factorize1(A+A-node(AA, _AACost), _Index, UnifsIn, UnifsOut) ==>
   {  put_attr(Two, const, 2),
      UnifsIn = [A2=AA | UnifsOut]
   },
   % make sure to use rationals for fractional costs
   % so that clpBNR cost variables always bounds to concrete values
   [2-node(Two, 1), A*Two-node(A2, 9r10)].
factorize1(_, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.
factorize2(A+BA-AA, Index, UnifsIn, UnifsOut) ==>
   { rb_lookup(BA, Nodes, Index) },
   factorize2(Nodes, A, AA, UnifsIn, UnifsOut).
factorize2(_, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.
factorize2([B*A | Nodes], A, node(AA, AACost), UnifsIn, UnifsOut) ==>
   {  put_attr(One, const, 1),
      UnifsIn = [B1A=AA | UnifsTmp]
   },
   [1-node(One, 1), B+One-node(B1, 1), B1*A-node(B1A, 9r10)],
   factorize2(Nodes, A, node(AA, AACost), UnifsTmp, UnifsOut).
factorize2([_ | Nodes], A, AA, UnifsIn, UnifsOut) ==>
   factorize2(Nodes, A, AA, UnifsIn, UnifsOut).
factorize2([], _, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

constant_folding((A+B)-node(AB, _ABCost), _Index, UnifsIn, UnifsOut),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA+VB,
      put_attr(C, const, VC),
      UnifsIn = [C=AB | UnifsOut]
   },
   [VC-node(C, 1)].
constant_folding((A*B)-node(AB, _ABCost), _Index, UnifsIn, UnifsOut),
      get_attr(A, const, VA), get_attr(B, const, VB) ==>
   {  VC is VA*VB,
      put_attr(C, const, VC),
      UnifsIn = [C=AB | UnifsOut]
   },
   [VC-node(C, 1)].
constant_folding(_, _, UnifsIn, UnifsOut) ==> {UnifsIn = UnifsOut}.

rules([Rule | Rules], Index, Node, Unifs) -->
   call(Rule, Node, Index, Unifs, UnifsRest),
   rules(Rules, Index, Node, UnifsRest).
rules([], _, _, []) --> [].

make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   maplist([node(Id, _Cost)-Node, Id-Node]>>true, Pairs, IdPairs),
   group_pairs_by_key(IdPairs, Groups),
   ord_list_to_rbtree(Groups, Index).

match(Rules, Worklist, Index, Matches, Unifs) :-
   foldl(rules(Rules, Index), Worklist, AllUnifs, Matches, []),
   append(AllUnifs, Unifs).

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

merge_group([Sig-[H | T] | Nodes], [Sig-Node | Worklist], In, Out) :-
   foldl([node(Id, Cost), node(Id, PrevCost), node(Id, MinCost)]>>
         (MinCost is min(Cost, PrevCost)), T, H, Node),
   (  T == []
   -> Tmp = In
   ;  Tmp = true
   ),
   merge_group(Nodes, Worklist, Tmp, Out).
merge_group([], [], In, In).

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
