:- module(esimplify,[esimplify/2]).

:- use_module('../prolog/egraph.pl').

esimplify(Exp,SExp) :-
	phrase((
       add_term(Exp, Id),
       saturate([
         esimplify:comm_add,
         esimplify:assoc_add,
         esimplify:factorize_aa,
         esimplify:factorize_aba,
         esimplify:reduce_add0,
         esimplify:constant_folding,
         esimplify:distribute,
         esimplify:cancel_add_sub
      ]),
      extract(Id, SExp),
      []
   ), [], _Graph).
   % \+ cyclic_term(SExp).

% Algebraic rules
egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(assoc_add, A+(B+C), (A+B)+C).

% Rules with custom cost
egraph:rewrite(factorize_aa, A+A, 2*A, [cost(9r10)]).

% Rules with left-hand side conditions
egraph:rewrite(reduce_add0, A+B, [const(B, 0)], A, []).

% Rules with a Prolog body
egraph:rewrite(constant_folding, A+B, [const(A, VA), const(B, VB)], VC, [const(VC)]) :-
   VC is VA + VB.

% Dict support
egraph:rewrite(operator_fusion, array{op: array{op: A+B}+C}, array{op: A+B+C}).

egraph:rewrite(factorize_aba, A+B*A, A*(B+1), [cost(9r10)]).
egraph:rewrite(distribute, A*(B+C), A*B+A*C).
egraph:rewrite(cancel_add_sub, A+B-A, B).
