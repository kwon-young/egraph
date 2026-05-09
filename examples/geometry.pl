:- use_module(library(dcg/high_order)).
:- use_module('../prolog/egraph.pl').

egraph:rule(triangle, 
   [seg(A, B)-_, seg(B, C)-_, seg(C, A)-_], 
   [triangle(A, B, C)-_]
) :-
   A \== B, B \== C, A \== C.

egraph:rule(triangle_ineq,
   ['$NODE'(_)-A, '$NODE'(_)-B, '$NODE'(_)-C], % this can't be _-A, _-B, _-C
   [point(A, _), point(B, _), point(C, _)],
   [dist(A, B)-AB, dist(B, C)-BC, dist(C, A)-CA, (AB+BC)-ABC, (ABC > CA)-_],
   []
) :-
   A \== B, B \== C, A \== C.

egraph:merge_property(point, _V1, V2, V2).

egraph:analyze(point_atom, '$NODE'(P), [\+ point(true)], [point(true)]) :- atom(P).

egraph:rewrite(dist_sym, dist(A, B), dist(B, A)).

egraph:merge_property(dist, V, V, V).

egraph:rule(seg_dist, [seg(A, B)-AB], [], [dist(A, B)-D], [dist(AB, D)]).

egraph:rule(ruler,
            ['$NODE'(_)-A, '$NODE'(_)-B], [point(A, _), point(B, _)],
            [seg(A, B)-_], []) :-
   A \== B.

egraph:rule(compass,
            ['$NODE'(_)-Center, dist(Center, _)-D], [point(Center, _)],
            [circle(Center, D)-_], []
).

egraph:rule(intersect_cc,
   [circle(A, R)-AR, circle(B, R)-BR, dist(A, B)-R], [],
   [intersect(AR, BR, 0)-Top, intersect(AR, BR, 1)-Bottom,
    dist(Top, A)-R, dist(Top, B)-R, dist(Bottom, A)-R, dist(Bottom, B)-R],
   [point(Top, top), point(Bottom, bottom)]
) :-
   A \== B.

:- debug(egraph_compile).

egraph:rule(rhombus,
   [seg(A, B)-AB, seg(Top, Bottom)-TB,
    dist(A, Top)-DAB, dist(Top, B)-DAB,
    dist(A, Bottom)-DAB, dist(Bottom, B)-DAB],
   [dist(AB, DAB)],
   [midpoint(AB, TB)-M, dist(A, M)-AM, dist(B, M)-AM, (AM+AM)-DAB],
   [point(M, midpoint)]
) :-
   A \== Top, B \== Top,
   A \== Bottom, B \== Bottom,
   Top \== Bottom.

:- nodebug(egraph_compile).

match(Term), [Term] -->
   [Term].
match(Term), [X] -->
   [X],
   match(Term).

main(Triangle) :-
   phrase((
      add_term(seg(a, b), _AB),
      add_term(seg(b, c), _BC),
      add_term(seg(c, a), _CA),
      saturate([triangle]),
      match(triangle(_A, _B, _C)-node(ABC, _Cost)),
      extract_all(ABC, Triangle)
   ), [], _).
main2(Seg, EGraph) :-
   phrase((
      add_term(a, _A),
      add_term(b, _B),
      saturate([point_atom, ruler]),
      match(seg(_, _)-node(AB, _Cost)),
      extract_all(AB, Seg)
   ), [], EGraph).
main3(Triangle, EGraph) :-
   phrase((
      add_term(a, _A),
      add_term(b, _B),
      add_term(c, _C),
      saturate([point_atom, ruler, triangle]),
      match(triangle(_, _, _)-node(ABC, _)),
      extract_all(ABC, Triangle)
   ), [], EGraph).

main4(N, Midpoint) :-
   phrase(add_term(seg(a, b), _AB), [], EGraph),
   main4_(N, EGraph, Midpoint).


main4_(0, EGraph, Midpoint) => Midpoint = EGraph.
main4_(N, EGraph, Midpoint) =>
   phrase((
      saturate([ruler, compass]),
      saturate([
         rhombus,
         point_atom,
         seg_dist,
         dist_sym,
         intersect_cc
      ])
   ), EGraph, EGraph1),
   (  
      phrase((
         match(midpoint(_, _)-node(M, _Cost)),
         extract(M, Midpoint)
      ), EGraph1, _)
   -> true
   ;  N1 is N - 1,
      main4_(N1, EGraph1, Midpoint)
   ).
