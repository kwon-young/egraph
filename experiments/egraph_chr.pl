:- use_module(library(chr)).
:- chr_constraint eclass/2.
congruence @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.

% :- initialization(main,main).

% helper to insert ground terms into egraph
insert( T , E) :-
 ground(T),
 var(E),
 T =.. [F | Args],
 length(Args, N), length(Es, N),
 T2 =.. [F | Es],
 eclass(T2, E),
 maplist(insert, Args, Es).


main(_) :-  insert(f(f(a)), FFA), insert(a, A), FFA = A,  insert(f(f(f(f(a)))), _FFFFA),
            chr_show_store(true).
