:- use_module('../prolog/egraph.pl').

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
   phrase((
      add_term(Expr, Id),
      saturate([comm, assoc, factorize1, factorize2, constant_folding], N),
      saturate([reduce], N), % reduce with comm+assoc+factorize explodes
      extract(Id, R)
   ), [], _).
