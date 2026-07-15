:- module(clpegraph, [
   op(700, xfx, #=),
   op(700, xfx, ?#=),
   #= /2, ?#= /2,
   saturate/1, saturate/2, extract/2, extract_all/2
]).

:- use_module('../prolog/egraph.pl').
:- use_module(library(dcg/high_order)).


:- nb_setval(min, _Min).
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

:- meta_predicate saturate(:).
:- meta_predicate saturate(:, +).

saturate(M:Rules) :-
   saturate(M:Rules, inf).
saturate(M:Rules, N) :-
   b_getval(egraph, In),
   saturate(M:Rules, N, In, Out),
   b_setval(egraph, Out).

extract(Id, Term) :-
   b_getval(egraph, EGraph),
   extract(Id, Term, EGraph, _).
extract_all(Id, Term) :-
   b_getval(egraph, EGraph),
   extract_all(Id, Term, EGraph, _).

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
   sort(Context, SortedContext),
   phrase((
      egraph:add_term(Left, Id, [var(class), mark(true)]),
      egraph:add_term(Right, Id, [var(class), mark(true)])
   ), [], Nodes),
   b_getval(egraph, In),
   foldl(runtime_traversal(In), Nodes, SortedContext, _).

runtime_traversal([Node | _], Pat, In, Sort) :-
   subsumes_term(In-Pat, In-Node),
   Node = Pat,
   term_variables(Pat, Out, In),
   % debug(runtime_traversal, "~p", [Pat]),
   sort(Out, Sort).
   % print_term(Pat-Sort, []), nl.
runtime_traversal([_ | Nodes], Pat, In, Out) :-
   runtime_traversal(Nodes, Pat, In, Out).

ord_memberchk_(L, E) :-
   ord_memberchk(E, L).
runtime_range_traversal(Nodes, Pat, In, Out) :-
   term_variables(Pat, Vars),
   exclude(ord_memberchk_(In), Vars, CopyVars),
   copy_term_nat(CopyVars, Pat, MinVars, MinPat),
   b_getval(min, Min),
   maplist(=(Min), MinVars),
   copy_term_nat(CopyVars, Pat, MaxVars, MaxPat),
   maplist(=(max), MaxVars),
   ord_range(Nodes, MinPat, MaxPat, Range),
   runtime_traversal(Range, Pat, In, Out).

ord_range([X1, X2, X3, X4|Xs], Min, Max, Range) =>
    (   X4 @< Min
    ->  ord_range(Xs, Min, Max, Range)
    ;   (   X2 @< Min
        ->  (   X3 @< Min
            ->  ord_take([X4 | Xs], Max, Range)
            ;   ord_take([X3, X4 | Xs], Max, Range)
            )
        ;   (   X1 @< Min
            ->  ord_take([X2, X3, X4 | Xs], Max, Range)
            ;   ord_take([X1, X2, X3, X4 | Xs], Max, Range)
            )
        )
    ).
ord_range([X1, X2 | Xs], Min, Max, Range) =>
    (   X2 @< Min
    ->  ord_range(Xs, Min, Max, Range)
    ;   (   X1 @< Min
        ->  ord_take([X2 | Xs], Max, Range)
        ;   ord_take([X1, X2 | Xs], Max, Range)
        )
    ).
ord_range([X], Min, Max, Range) =>
    (   X @>= Min, X @=< Max
    -> Range = [X]
    ;   Range = []
    ).
ord_range([], _Min, _Max, Range) =>
    Range = [].

ord_take([X1, X2, X3, X4|Xs], Max, Range) =>
    (   X4 @=< Max
    ->  Range = [X1, X2, X3, X4|Rest],
        ord_take(Xs, Max, Rest)
    ;   (   X2 @=< Max
        ->  (   X3 @=< Max
            ->  Range = [X1, X2, X3]
            ;   Range = [X1, X2]
            )
        ;   (   X1 @=< Max
            ->  Range = [X1]
            ;   Range = []
            )
        )
    ).
ord_take([X1, X2 | Xs], Max, Range) =>
    (   X2 @=< Max
    ->  Range = [X1, X2 | Rest],
        ord_take(Xs, Max, Rest)
    ;   (   X1 @=< Max
        ->  Range = [X1]
        ;   Range = []
        )
    ).
ord_take([X], Max, Range) =>
    (   X @=< Max
    ->  Range = [X]
    ;   Range = []
    ).
ord_take([], _Max, Range) =>
    Range = [].

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

triangle(T) :-
   _AB ?#= seg(A, B),
   _BC ?#= seg(B, C),
   _CA ?#= seg(C, A),
   T #= triangle(A, B, C).
example4(T) :-
   _AB #= seg(a, b),
   _BC #= seg(b, c),
   _CA #= seg(c, d),
   a #= d,
   triangle(T).
