:- use_module('../prolog/egraph.pl').

:- debug(egraph_compile).

egraph:merge_property(const, V1, V2, Merged) :-
   (  V1 =:= V2
   -> Merged = V1
   ;  domain_error(V1, V2)
   ).
%
egraph:analyze(is_const, '$NODE'(A), [const(A)]) :- number(A).
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
               '$NODE'(VC), [const(VC)]) :-
   VC is VA+VB.
egraph:rewrite(operator_fusion, array{op: array{op: A+B}+C}, array{op: A+B+C}).
egraph:rewrite(var_match, f('$NODE'(X)), g('$NODE'(X))) :- var(X).
egraph:rewrite(distribute, A*(B+C), A*B+A*C).
egraph:rewrite(cancel_add_sub, A+B-A, B).
egraph:rewrite(test_early_cut, f(b), success).
egraph:rule(test_early_cut2, [f(X)-_, g(X)-_], [], [], []) :-
   b_setval(test_early_cut_fired, true).
egraph:rule(existential_fail, [f(A)-_, g(A)-_], [], [], []).

add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

example2(N, Expr) :-
   add_expr(N, Expr),
   phrase(add_term(Expr, _), [], G),
   time(saturate([comm_add, assoc_add], G, G1)),
   length(G1, N1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   print_term(N1-Num, []), nl.

:- begin_tests(rules, [timeout(1)]).

rule_test(X+Y, [comm_add], X+Y, [Y+X, X+Y]).
rule_test(a+b, [comm_add], a+b, [b+a, a+b]).
rule_test(a*b, [comm_mul], a*b, [b*a, a*b]).
rule_test(a+(b+c), [assoc_add], a+(b+c), [a+b+c, a+(b+c)]).
rule_test(a*(b*c), [assoc_mul], a*(b*c), [a*b*c, a*(b*c)]).
rule_test(a+0, [reduce_add0], a, [a, a+0]).
rule_test(a*1, [reduce_mul1], a, [a, a*1]).
rule_test(a*0, [reduce_mul0], 0, [0, a*0]).
rule_test(a+a, [factorize_aa], 2*a, [a+a, 2*a]).
rule_test(a+b*a, [factorize_aba], a*(b+1), [a+b*a, a*(b+1)]).
rule_test(2+3, [constant_folding], 5, [5, 2+3]).
rule_test(array{op: array{op: 1+2}+3}, [operator_fusion], array{op: 1+2+3}, [array{op: 1+2+3}, array{op: array{op: 1+2}+3}]).
rule_test(f(X), [var_match], f(X), [g(X), f(X)]).
% Case 1: Symbolic Factorization
rule_test(x+y*x, [factorize_aba], x*(y+1), [x+y*x, x*(y+1)]).
% Case 2: Non-Greedy Rewriting (The Valley Problem)
rule_test(a*(x+y) - a*x, [distribute, cancel_add_sub], a*y, [a*y, a*(x+y) - a*x]).
rule_test(f(a) + f(b), [test_early_cut], f(a) + success, [f(a) + success, f(a) + f(b)]).

test(rewrite, [forall(rule_test(Term, Rules, Expected, _ExpectedAll)), Extracted =@= Expected]) :-
   phrase((
      add_term(Term, T),
      saturate([is_const]),
      saturate(Rules),
      extract(T, Extracted)), [], _),
   print_term(Extracted =@= Expected, []), nl.
test(rewrite_all, [forall(rule_test(Term, Rules, _, Expected)), Terms =@= Expected]) :-
   findall(Extracted-Term,
      limit(2, 
         phrase((
            add_term(Term, T),
            saturate([is_const]),
            saturate(Rules),
            extract_all(T, Extracted)), [], _)
      ), Pairs),
   pairs_keys_values(Pairs, Terms, Copies),
   maplist(=(Term), Copies),
   print_term(Terms =@= Expected, []), nl.

test(dict) :-
   phrase((
      add_term(array{op: a+b}, T),
      saturate([comm_add]),
      extract(T, Extracted)
   ), [], _),
   Extracted.op == (a+b).

test(existential_cut) :-
   b_setval(test_early_cut_fired, false),
   phrase((
      add_term(f(a), _),
      add_term(f(b), _),
      add_term(g(b), _),
      saturate([test_early_cut2])
   ), [], _),
   b_getval(test_early_cut_fired, true).

test(existential_fail_succeeds) :-
   % This rule should succeed even if no full match is found.
   % The bug causes saturate/1 to fail entirely.
   phrase((
      add_term(f(a), _),
      saturate([existential_fail])
   ), [], _).

:- end_tests(rules).
