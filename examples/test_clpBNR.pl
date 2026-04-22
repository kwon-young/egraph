:- module(test_clpBNR, []).
:- use_module('../prolog/egraph.pl').

:- debug(egraph_compile).

% Commutativity and Associativity for addition
egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(assoc_add, A+(B+C), (A+B)+C).

% Factoring identical terms
egraph:rewrite(factorize_add, A+A, 2*A, [cost(9r10)]).

% Zero reduction
egraph:rewrite(reduce_add0, A+B, [const(B, 0)], A, []).

% Factoring terms with constant multipliers
egraph:rewrite(factor_add1, N*A+A, (N+1)*A, [cost(9r10)]).

% Factoring two multiplier terms
egraph:rewrite(factor_add, N1*A+N2*A, (N1+N2)*A).

egraph:rewrite(constant_folding_add, A+B, [const(A, VA), const(B, VB)], VC, [const(VC)]) :-
   VC is VA + VB.

:- begin_tests(clpbnr_simplify).

rule_test(A, A).
rule_test(A+0, A).
rule_test(A+A, 2*A).
rule_test(A+A+A, 3*A).
rule_test(A+A+A+A, 4*A).
rule_test(A+0+A, 2*A).
rule_test(A+B+A, B+2*A).
rule_test(A+B+A+B, 2*(A+B)).
rule_test(A+0+1, A+1).

test(simplify, [forall(rule_test(Term, Expected))]) :-
   Rules = [ comm_add, assoc_add, factorize_add, factor_add1, factor_add ],
   phrase((
      add_term(Term, T),
      saturate(Rules),
      saturate([reduce_add0, constant_folding_add]),
      extract(T, Extracted)
   ), [], _),
   print_term((Term, Extracted =@= Expected), []), nl,
   Extracted =@= Expected.

:- end_tests(clpbnr_simplify).
