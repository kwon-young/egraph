:- module(test_clpBNR, [simplify/2, simplify/3]).

/** <module> test_clpBNR

Features of clpBNR's ia_simplify.pl:
  * Precise vs Imprecise numbers: Expression variables are Prolog vars. Precise numeric 
    constants (rationals/integers) are evaluated, while floats are treated as symbolic 
    variables (no arithmetic is performed on them).
  * Distribution: Distributes constants over addition/subtraction, e.g., C*(A+B) -> C*A + C*B 
    (if C is a precise number).
  * Equality/Inequality Normalization: Simplifies relational operators (==, =<, >=, <, >) by 
    separating numeric constants to the RHS and moving symbolic variable expressions to the LHS.
  * Constant Folding: Precise numbers are aggregated and evaluated for addition, multiplication, 
    negation, and inversion.
  * Algebraic Simplifications:
    - Combines identical symbolic terms (e.g., N1*V + N2*V -> (N1+N2)*V).
    - Power simplification: (A**P)**NT -> A**(P*NT) when P and NT are rational.
  * Safety Limits: Avoids unsafe algebraic rules on infinities (e.g., 1.0Inf) and only 
    reduces 0*V -> 0 if V is proven to be finite.
*/

:- use_module('../prolog/egraph.pl').
:- use_module(library(clpBNR)).

% :- debug(egraph_compile).

% in/equalities normalization
egraph:rewrite(eq_left, A == B, A - B == 0).
egraph:rewrite(le_left, A =< B, A - B =< 0).
egraph:rewrite(ge_left, A >= B, A - B >= 0).
egraph:rewrite(lt_left, A < B, A - B < 0).
egraph:rewrite(gt_left, A > B, A - B > 0).
% Normalize
egraph:rewrite(sub_to_add, A - B, A + -1 * B).
egraph:rewrite(neg_to_mul, -A, -1 * A).
egraph:rewrite(div_to_mul, A / B, A * B** -1).

% Analyze
egraph:merge_property(precise, V1, V2, Merged) :-
   (  V1 =:= V2
   -> Merged = V1
   ;  domain_error(V1, V2)
   ).
egraph:merge_property(finite, V1, V2, Merged) :-
   (  V1 == V2, V1 == true
   -> Merged = V1
   ;  domain_error(V1, V2)
   ).
egraph:analyze(is_precise, '$NODE'(A), [precise(A), finite(true)]) :- rational(A).
egraph:analyze(is_finite, '$NODE'(A), [finite(true)]) :-
   (  float(A), abs(A) =\= 1.0Inf
   ;  var(A), interval(A), range(A, [L, U]), -1.0Inf < L, U < 1.0Inf
   ).
egraph:analyze(cf_add, A+B, [precise(A, VA), precise(B, VB)], [precise(VC)]) :-
   VC is VA+VB.
egraph:analyze(cf_mul, A*B, [precise(A, VA), precise(B, VB)], [precise(VC)]) :-
   VC is VA*VB.
egraph:analyze(cf_pow, A**B, [precise(A, VA), precise(B, VB)], [precise(VC)]) :-
   VC is VA**VB.
egraph:analyze(cf_mul0, A*B, [precise(B, 0), finite(A, true)], [precise(0)]).
egraph:analyze(cf_pow0, A**B, [precise(B, 0), finite(A, true)], [precise(1)]).

% Distribute
egraph:rewrite(distribute_add, C*(A+B), C*A+C*B).

% Factorize
egraph:rewrite(factorize_add0, A+A, 2*A, [cost(9r10)]).
egraph:rewrite(factorize_add1, N*A+A, (N+1)*A, [cost(9r10)]).
egraph:rewrite(factorize_add2, C1*V+C2*V, (C1+C2)*V).

egraph:rewrite(factorize_mul0, A*A, A**2, [cost(9r10)]).
egraph:rewrite(factorize_mul1, A**N*A, A**(N+1), [cost(9r10)]).
egraph:rewrite(factorize_mul2, V**C1 * V**C2, V**(C1+C2)).

egraph:rewrite(power_simplify, (A**P)**NT, [precise(P, _), precise(NT, _)], A**(P*NT), []).

% Reduce identities
egraph:rewrite(reduce_add, A+B, [precise(B, 0)], A, []).
egraph:rewrite(reduce_mul, A*B, [precise(B, 1)], A, []).
egraph:rewrite(reduce_pow, A**B, [precise(B, 1)], A, []).

% comm assoc
egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(assoc_add, A+(B+C), (A+B)+C).
egraph:rewrite(comm_mul, A*B, B*A).
egraph:rewrite(assoc_mul, A*(B*C), (A*B)*C).

% Finalize
% Use with constant folding
egraph:rewrite(eq_right, A+B == 0, [precise(B, _)], A == -1*B, []).
egraph:rewrite(le_right, A+B < 0, [precise(B, _)], A < -1*B, []).
egraph:rewrite(ge_right, A+B > 0, [precise(B, _)], A > -1*B, []).
egraph:rewrite(lt_right, A+B =< 0, [precise(B, _)], A =< -1*B, []).
egraph:rewrite(gt_right, A+B >= 0, [precise(B, _)], A >= -1*B, []).

egraph:rewrite(replace_precise, '$NODE'(_), [precise(V)], '$NODE'(V), []).

simplify(In, Out) :-
   simplify(In, Out, _).
simplify(In, Out, EGraph) :-
   EqLeft = [eq_left, le_left, ge_left, lt_left, gt_left],
   Normalize = [sub_to_add, neg_to_mul, div_to_mul],
   Analyze = [is_precise, is_finite],
   CommAssoc = [comm_add, assoc_add, comm_mul, assoc_mul],
   ConstantFolding = [cf_add, cf_mul, cf_pow, cf_mul0, cf_pow0 | CommAssoc],
   Explodes = [distribute_add, factorize_add0, factorize_add1, factorize_add2, power_simplify | ConstantFolding],
   Merges = [reduce_add, reduce_mul, reduce_pow | ConstantFolding],
   EqRight = [eq_right, le_right, ge_right, lt_right, gt_right],
   phrase((
      egraph:add_terms([-1, 0, 1, 2], _, []),
      add_term(In, Id),
      saturate(EqLeft, 1),
      saturate(Normalize, 1),
      saturate(Analyze, 1),
      saturate(Explodes),
      saturate(Merges),
      saturate(EqRight, 1),
      saturate(ConstantFolding),
      saturate([replace_precise], 1),
      extract_all(Id, Out)
   ), [], EGraph).

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
rule_test(0.1+0.2, 0.1+0.2).

test(simplify, [forall(rule_test(Term, Expected))]) :-
   Rules = [is_const, comm_add, assoc_add, factorize_add, factor_add1, factor_add],
   phrase((
      add_term(Term, T),
      saturate(Rules),
      saturate([is_const, reduce_add0, cf_add]),
      extract(T, Extracted)
   ), [], _),
   print_term((Term, Extracted =@= Expected), []), nl,
   Extracted =@= Expected.

:- end_tests(clpbnr_simplify).
