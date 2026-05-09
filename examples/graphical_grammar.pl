:- use_module('../prolog/egraph.pl').

% :- debug(egraph_compile).
egraph:rule(triangle,
            [seg(A, B)-_, seg(B, C)-_, seg(C, A)-_], [triangle(A, B, C)-_]) :-
   A \== B, B \== C, A \== C.

dist(point(X1, Y1), point(X2, Y2), Dist) :-
   Dist is (X2 - X1)**2 + (Y2 - Y1)**2.

egraph:merge_property(point, point(X1, Y1), point(X2, Y2), point(X3, Y3)) :-
   X3 is (X1 + X2) / 2,
   Y3 is (Y1 + Y2) / 2.
egraph:merge_property(dist, D1, D2, D) :-
   D is (D1 + D2) / 2.

egraph:analyze(is_point, point('$NODE'(X), '$NODE'(Y)), [point(point(X, Y))]).
egraph:rule(dist_pp, ['$NODE'(_)-I1, '$NODE'(_)-I2], [point(I1, P1), point(I2, P2)],
                     [dist(I1, I2)-D], [dist(D, Dist)]) :-
   I1 \== I2,
   dist(P1, P2, Dist).

egraph:rewrite(dist_sym, dist(A, B), dist(B, A)).
egraph:rewrite(seg_sym, seg(A, B), seg(B, A)).

egraph:rule(merge, [dist(I1, I2)-D], [dist(D, Dist)], [I1-I2], []) :-
   Dist < 0.5.

setup(T) :-
   T = triangle(_, _, _),
   phrase((
      add_term(seg(point(0, 0), point(1, 1)), _),
      add_term(seg(point(0.1, 0), point(0, 1)), _),
      add_term(seg(point(0, 1.1), point(1.1, 1)), _),
      saturate([is_point]),
      saturate([dist_pp]),
      saturate([dist_sym, seg_sym]),
      saturate([merge]),
      saturate([triangle]),
      query(T)
   ), [], _).

