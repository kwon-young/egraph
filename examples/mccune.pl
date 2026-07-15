:- use_module('../prolog/egraph.pl').

% 2. Apply Axioms as Rules
egraph:rewrite(id_left, e*X, X).
egraph:rewrite(inv_left, inv(X)*X, e).
egraph:rewrite(assoc, X*(Y*Z), (X*Y)*Z).

% Helper to generate the operation space
generate_domain(N) -->
   { numlist(1, N, Elements) },
   egraph:add_terms(Elements, _, []),
   { findall(X*Y, (member(X, Elements), member(Y, Elements)), Muls) },
   { findall(inv(X), member(X, Elements), Invs) },
   egraph:add_terms(Muls, _, []),
   egraph:add_terms(Invs, _, []).

mccune_model_setup :-
   phrase((
      % 1. Define the Domain & Assign Constants
      add_term(e, E), add_term(1, One),
      add_term(c, C), add_term(2, Two),
      add_term(d, D), add_term(3, Three),
      union(E, One),
      union(C, Two),
      union(D, Three),
      % Generate the operation space for 6 elements
      generate_domain(6)
   ), [], In),
   time(phrase(
      % Saturate the graph using the axiom rewrite rules
      saturate([id_left, inv_left, assoc]),
      In, Out
   )),
   phrase((
      % Retrieve the e-class IDs for c*d and d*c
      add_term(c*d, IdCD),
      add_term(d*c, IdDC)
   ), Out, _Graph),
   
   % 4. Verify Constraint: ensure c*d \= d*c are in different equivalence classes
   IdCD \== IdDC.

% :- begin_tests(mccune).
%
% :- end_tests(mccune).
