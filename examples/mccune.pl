:- use_module('../prolog/egraph.pl').

% 2. Apply Axioms as Rules
egraph:rewrite(id_left, e*X, X).
egraph:rewrite(inv_left, inv(X)*X, e).
egraph:rewrite(assoc, X*(Y*Z), (X*Y)*Z).

% Helper to generate the operation space
generate_domain(N) -->
   { numlist(1, N, Elements) },
   add_terms(Elements, _),
   { findall(X*Y, (member(X, Elements), member(Y, Elements)), Muls) },
   { findall(inv(X), member(X, Elements), Invs) },
   add_terms(Muls, _),
   add_terms(Invs, _).

:- begin_tests(mccune).

test(mccune_model_setup) :-
   phrase((
      % 1. Define the Domain & Assign Constants
      add_term(e, IdE), add_term(1, IdE),
      add_term(c, IdC), add_term(2, IdC),
      add_term(d, IdD), add_term(3, IdD),
      
      % Generate the operation space for 6 elements
      generate_domain(6),
      
      % Saturate the graph using the axiom rewrite rules
      saturate([id_left, inv_left, assoc]),
      
      % Retrieve the e-class IDs for c*d and d*c
      add_term(c*d, IdCD),
      add_term(d*c, IdDC)
   ), [], _Graph),
   
   % 4. Verify Constraint: ensure c*d \= d*c are in different equivalence classes
   IdCD \== IdDC.

:- end_tests(mccune).
