:- module(test_clpBNR, []).
:- use_module('../prolog/egraph.pl').

:- debug(egraph_compile).

% Commutativity and Associativity for addition
egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(assoc_add, A+(B+C), (A+B)+C).

% Zero reduction
egraph:rewrite(reduce_add0, A+B, [const(B, 0)], A, []).

% Factoring identical terms
egraph:rewrite(factorize_aa, A+A, 2*A, [cost(9r10)]).

% Factoring terms with constant multipliers
egraph:rewrite(factorize_naa, N*A+A, [const(N, VN)], M*A, [const(M)]) :- 
    M is VN + 1.

egraph:rewrite(factorize_ana, A+N*A, [const(N, VN)], M*A, [const(M)]) :- 
    M is VN + 1.

% Factoring two multiplier terms
egraph:rewrite(factorize_nma, N*A+M*A, [const(N, VN), const(M, VM)], K*A, [const(K)]) :- 
    K is VN + VM.

% Factoring identical multipliers over addition
egraph:rewrite(factorize_dist, N*A+N*B, [], N*(A+B), []).


:- begin_tests(clpbnr_simplify).

rule_test(A, A).
rule_test(A+0, A).
rule_test(A+A, 2*A).
rule_test(A+A+A, 3*A).
rule_test(A+A+A+A, 4*A).
rule_test(A+0+A, 2*A).
rule_test(A+B+A, B+2*A).
rule_test(A+B+A+B, 2*(A+B)).

test(simplify, [forall(rule_test(Term, Expected))]) :-
   Rules = [
      comm_add, assoc_add, factorize_aa,
      factorize_naa, factorize_ana, factorize_nma, factorize_dist
   ],
   phrase((
      add_term(Term, T),
      saturate(Rules),
      saturate([reduce_add0]),
      extract(T, Extracted)
   ), [], _),
   print_term((Term, Extracted =@= Expected), []), nl,
   Extracted =@= Expected.

:- end_tests(clpbnr_simplify).
