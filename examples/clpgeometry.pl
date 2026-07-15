:- use_module('../prolog/egraph.pl').
:- use_module(clpegraph).

ruler(AB) :-
   A ?#= point(_),
   B ?#= point(_),
   A \== B,
   \+ _ ?#= seg(A, B),
   AB #= seg(A, B).

compass(Circle) :-
   A ?#= point(_),
   D ?#= dist(A, _),
   \+ _ ?#= circle(A, D),
   Circle #= circle(A, D).

egraph:rewrite(dist_sym, dist(A, B), dist(B, A)).

egraph:merge_property(dist, V, V, V).

egraph:rule(seg_dist, [seg(A, B)-AB], [], [dist(A, B)-D], [dist(AB, D)]).

egraph:rule(intersect_cc,
   [circle(A, R)-AR, circle(B, R)-BR, dist(A, B)-R],
   [point(intersect(AR, BR, 0))-Top, point(intersect(AR, BR, 1))-Bottom,
    dist(Top, A)-R, dist(Top, B)-R, dist(Bottom, A)-R, dist(Bottom, B)-R]
).

egraph:rule(rhombus,
   [seg(A, B)-AB, seg(Top, Bottom)-TB,
    dist(A, Top)-D, dist(Top, B)-D,
    dist(A, Bottom)-D, dist(Bottom, B)-D],
   [dist(AB, DAB)],
   [point(midpoint(AB, TB))-M, dist(A, M)-AM, dist(B, M)-AM, (AM+AM)-DAB],
   []
) :-
   D == DAB,
   A \== Top, B \== Top,
   A \== Bottom, B \== Bottom,
   Top \== Bottom.

saturate :-
   saturate([
      rhombus,
      seg_dist,
      dist_sym,
      intersect_cc
   ]).

setup(Seg) :-
   Seg #= seg(point(a), point(b)),
   saturate.

build(Figure) :-
   (ruler(Figure) ; compass(Figure)),
   saturate.
