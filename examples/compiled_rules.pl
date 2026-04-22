:- module(compiled_rules, [comm_add//5, comm_mul//5, assoc_add//5, assoc_mul//5,
                           reduce_add0//5, reduce_mul1//5, reduce_mul0//5,
                           factorize_aa//5, factorize_aba//5,
                           constant_folding//5, operator_fusion//5,
                           var_match//5,
                           distribute//5, cancel_add_sub//5]).
:- use_module('../prolog/egraph.pl').

egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(comm_mul, A*B, B*A).
egraph:rewrite(assoc_add, A+(B+C), (A+B)+C).
egraph:rewrite(assoc_mul, A*(B*C), (A*B)*C).
egraph:rewrite(reduce_add0, A+B, [const(B, 0)], A, []).
egraph:rewrite(reduce_mul1, A*B, [const(B, 1)], A, []).
egraph:rewrite(reduce_mul0, _*B, [const(B, 0)], B, []).
egraph:rewrite(factorize_aa, A+A, 2*A, [cost(9r10)]).
egraph:rewrite(factorize_aba, A+B*A, A*(B+1), [cost(9r10)]).
egraph:rewrite(constant_folding, A+B, [const(A, VA), const(B, VB)],
               VC, [const(VC)]) :-
   VC is VA+VB.
egraph:rewrite(operator_fusion, array{op: array{op: A+B}+C}, array{op: A+B+C}).
egraph:rewrite(var_match, f('$NODE'(X)), g(X)) :- var(X).
egraph:rewrite(distribute, A*(B+C), A*B+A*C).
egraph:rewrite(cancel_add_sub, A+B-A, B).

add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add_term(Expr, _), [], G),
   time(saturate([comm_add, assoc_add], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

:- begin_tests(rules).

rule_test(X+Y, [comm_add], X+Y, [Y+X, X+Y]).
rule_test(a+b, [comm_add], a+b, [b+a, a+b]).
rule_test(a*b, [comm_mul], a*b, [b*a, a*b]).
rule_test(a+(b+c), [assoc_add], a+(b+c), [a+b+c, a+(b+c)]).
rule_test(a*(b*c), [assoc_mul], a*(b*c), [a*b*c, a*(b*c)]).
rule_test(a+0, [is_const, reduce_add0], a, [a, a+0]).
rule_test(a*1, [is_const, reduce_mul1], a, [a, a*1]).
rule_test(a*0, [is_const, reduce_mul0], 0, [0, a*0]).
rule_test(a+a, [factorize_aa], 2*a, [2*a, a+a]).
rule_test(a+b*a, [factorize_aba], a*(b+1), [a*(b+1), a+b*a]).
rule_test(2+3, [is_const, constant_folding], 5, [5, 2+3]).
rule_test(array{op: array{op: 1+2}+3}, [operator_fusion], array{op: 1+2+3}, [array{op: 1+2+3}, array{op: array{op: 1+2}+3}]).
rule_test(f(X), [var_match], f(X), [g(X), f(X)]).
% Case 1: Symbolic Factorization
rule_test(x+y*x, [factorize_aba], x*(y+1), [x*(y+1), x+y*x]).
% Case 2: Non-Greedy Rewriting (The Valley Problem)
rule_test(a*(x+y) - a*x, [distribute, cancel_add_sub], a*y, [a*y, a*(x+y) - a*x]).

test(rewrite, [forall(rule_test(Term, Rules, Expected, _ExpectedAll))]) :-
   phrase((
      add_term(Term, T),
      saturate(Rules),
      extract(T, Extracted)), [], _),
   print_term(Extracted =@= Expected, []), nl,
   Extracted =@= Expected.
test(rewrite_all, [forall(rule_test(Term, Rules, _, Expected))]) :-
   findall(Extracted-Term,
      limit(2, 
         phrase((
            add_term(Term, T),
            saturate(Rules),
            extract_all(T, Extracted)), [], _)
      ), Pairs),
   pairs_keys_values(Pairs, Terms, Copies),
   maplist(=(Term), Copies),
   print_term(Terms =@= Expected, []), nl,
   % exclude(cyclic_term, Terms, AcyclicTerms),
   Terms =@= Expected.

test(dict) :-
   phrase((
      add_term(array{op: a+b}, T),
      saturate([comm_add]),
      extract(T, Extracted)
   ), [], _),
   Extracted.op == (a+b).

:- end_tests(rules).
