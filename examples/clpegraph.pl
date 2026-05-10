:- use_module('../prolog/egraph.pl').
:- use_module(library(dcg/high_order)).

:- op(700, xfx, #=).
:- op(700, xfx, ?#=).

:- nb_setval(egraph, []).

get_egraph(EGraph) :-
   b_getval(egraph, EGraph).

egraph:attr_unify_hook(true, Y) :-
   (  var(Y)
   -> get_egraph(In),
      egraph:merge_nodes(In, Out),
      b_setval(egraph, Out)
   ;  domain_error(var, Y)
   ).

egraph:attribute_goals(Var) -->
   {  get_attr(Var, egraph, true),
      b_getval(egraph, In),
      extract(Var, Term, In, _)
   },
   [Var #= Term].

'#='(Left, Right) :-
   get_egraph(In),
   phrase((
      egraph:add_term(Left, LeftId, [var(class), mark(true)]),
      egraph:add_term(Right, RightId, [var(class), mark(true)]),
      union(LeftId, RightId)
   ), In, Out),
   b_setval(egraph, Out).

% e-matching
'?#='(Left, Right),
      get_attr(Left, egraph, true),
      get_attr(Right, egraph, true) =>
   Left == Right.
'?#='(Left, Right) =>
   term_variables(Left-Right, Vars),
   include([V]>>get_attr(V, egraph, _), Vars, Context),
   phrase((
      egraph:add_term(Left, Id, [var(class), mark(true)]),
      egraph:add_term(Right, Id, [var(class), mark(true)])
   ), [], Nodes),
   b_getval(egraph, In),
   foldl(runtime_traversal(In), Nodes, Context, _).

runtime_traversal([Node | _], Pat, In, Out) :-
   subsumes_term(In-Pat, In-Node),
   Node = Pat,
   term_variables(Pat, Out, In).
runtime_traversal([_ | Nodes], Pat, In, Out) :-
   runtime_traversal(Nodes, Pat, In, Out).

example1(A, FFA, FFFFA) :-
   % ?- A #= a, FFA #= f(f(a)), A = FFA, FFFFA #= f(f(f(f(a)))).
   % A = FFA, FFA = FFFFA,
   % FFFFA#=a,
   % FFFFA#=f(f(a)),
   % FFFFA#=f(f(f(f(a)))).
   A #= a,
   FFA #= f(f(a)),
   A = FFA,
FFFFA #= f(f(f(f(a)))).

example2 :-
   \+ (
      A #= a, B #= b, C #= c,
      FA #= f(a), FC #= f(c),
      dif(FA, FC),
      A = B, B = C
   ).

example3 :-
   _FFA #= f(f(a)),
   a ?#= A,
   _FA ?#= f(A).
