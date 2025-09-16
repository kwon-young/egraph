:- module(egraph_rules, [comm_add//5, comm_mul//5, assoc_add//5, assoc_mul//5,
                         reduce_add0//5, reduce_mul1//5, reduce_mul0//5,
                         factorize_aa//5, factorize_aba//5,
                         constant_folding//5]).
:- use_module(egraph).
:- use_module(egraph_compile).

egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(comm_mul, A*B, B*A).
egraph:rewrite(assoc_add, (A+B)+C, A+(B+C)).
egraph:rewrite(assoc_mul, (A*B)*C, A*(B*C)).
egraph:rewrite(reduce_add0, A+B, [get_attr(B, const, 0)], A, []).
egraph:rewrite(reduce_mul1, A*B, [get_attr(B, const, 1)], A, []).
egraph:rewrite(reduce_mul0, _*B, [get_attr(B, const, 0)], B, []).
egraph:rewrite(factorize_aa, A+A, Two*A, [put_attr(Two, const, 2), cost(9r10)]).
egraph:rewrite(factorize_aba, A+B*A, A*(B+One), [put_attr(One, const, 1), cost(9r10)]).
egraph:rewrite(constant_folding, A+B, [get_attr(A, const, VA), get_attr(B, const, VB)],
               C, [put_attr(C, const, VC)]) :-
   VC is VA+VB.

:- begin_tests(rules).

rule_test(a+b, comm_add, [a+b, b+a]).
rule_test(a*b, comm_mul, [a*b, b*a]).
rule_test((a+b)+c, assoc_add, [(a+b)+c, a+(b+c)]).
rule_test((a*b)*c, assoc_mul, [(a*b)*c, a*(b*c)]).
rule_test(a+0, reduce_add0, [a+0, a]).
rule_test(a*1, reduce_mul1, [a*1, a]).
rule_test(a*0, reduce_mul0, [a*0, 0]).
rule_test(a+a, factorize_aa, [a+a, 2*a]).
rule_test(a+b*a, factorize_aba, [a+b*a, a*(b+1)]).
rule_test(2+3, constant_folding, [5, 2+3]).

test(rewrite, [forall(rule_test(Term, Rule, Expected))]) :-
   findall(T,
      phrase((
         add_term(Term, T),
         saturate([Rule]),
         extract), [], _),
      Terms),
   print_term(Terms, []),
   sort(Terms, Sorted),
   sort(Expected, SortedExpected),
   Sorted == SortedExpected.

:- end_tests(rules).
