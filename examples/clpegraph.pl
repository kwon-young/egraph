:- use_module(library(egraph)).
:- use_module(library(dcg/high_order)).

:- op(700, xfx, #=).

:- nb_setval(egraph, []).

get_egraph(EGraph) :-
   b_getval(egraph, EGraph).

egraph:attr_unify_hook(XTerm, Y) :-
   (  var(Y)
   -> get_egraph(In),
      egraph:merge_nodes(In, Out),
      b_setval(egraph, Out),
      get_attr(Y, egraph, YTerm),
      put_attr(Y, egraph, (YTerm ; XTerm))
   ;  domain_error(var, XTerm-Y)
   ).

egraph:attribute_goals(Var) -->
   {  get_attr(Var, egraph, Term),
      semicolon_list(Term, L)
   },
   sequence(portray_(Var), L).

portray_(Var, Term) -->
   [Var #= Term].

'#='(Var, Term) :-
   get_egraph(In),
   put_attr(Id, egraph, Term),
   add_term(Term, Id, In, Out),
   Var = Id,
   b_setval(egraph, Out).

example1(A, FFA, FFFFA) :-
   % ?- A #= a, FFA #= f(f(a)), A = FFA, FFFFA #= f(f(f(f(a)))).
   % A = FFA, FFA = FFFFA,
   % FFFFA#=a,
   % FFFFA#=f(f(a)),
   % FFFFA#=f(f(f(f(a)))).
   A #= a,
   FFA #= f(f(a)),
   A = FFA,
   FFFFA #= f(f(f(f(a)))).

example2 :-
   \+ (
      A #= a, B #= b, C #= c,
      FA #= f(a), FC #= f(c),
      dif(FA, FC),
      A = B, B = C
   ).
