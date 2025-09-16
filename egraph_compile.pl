:- module(egraph_compile, []).

:- use_module(library(dcg/high_order)).

compile(rewrite(Name, Left, LeftOptions, Right, RightOptions) :- Body) -->
   {term_nodes(Left-Id, [Pat-_ | T])},
   compile_nodes(T, Name, Pat, [], Id, LeftOptions, Right, RightOptions, Body).

common_variables(A, B) :-
   term_variables(A, VAs),
   term_variables(B, VBs),
   list_to_ord_set(VAs, ASet),
   list_to_ord_set(VBs, BSet),
   ord_intersect(ASet, BSet).

compile_nodes([NextPat-node(NextId, _) | Nodes], Name, Pat, Pats, Id, LeftOptions, Right, RightOptions, SubBody) ==>
   {
      append(Pats, [_UnifsIn, _UnifsOut], Args),
      Head =.. [Name, Pat, Id, Index | Args],
      atom_concat(Name, '_', NewName),
      SubCall =.. [NewName, NextIdNodes, Id, Index | [Pat | Args]],
      Body = (
         {rb_lookup(NextId, NextIdNodes, Index)},
         SubCall
      ),
      partition(common_variables(Pat), LeftOptions, GuardList, LeftRest),
      (  comma_list(Guard, GuardList)
      -> HeadGuard = (Head, Guard)
      ;  HeadGuard = Head
      ),
      append([Pat | GuardList], Pats, AllPats)
   },
   assert_rule(HeadGuard ==> Body),
   default_clause(Head),
   compile_iter_nodes(Nodes, NewName, NextPat, AllPats, Id, LeftRest, Right, RightOptions, SubBody).
compile_nodes([], Name, Pat, Pats, Id, LeftOptions, Right, RightOptions, SubBody) ==>
   {
      append(Pats, [UnifsIn, UnifsOut], Args),
      Head =.. [Name, Pat, Id, _Index | Args],
      term_nodes(Right-NewId, RightNodes),
      (  RightNodes = [_-node(_, Cost) | RightTail]
      -> select_option(cost(Cost), RightOptions, RightRest, 1),
         maplist(=(_-node(_, 1)), RightTail)
      ;  RightRest = RightOptions
      ),
      reverse(RightNodes, RRightNodes),
      (  comma_list(RightBody, RightRest)
      -> true
      ;  RightBody = true
      ),
      foldl(mkconj, [SubBody, RightBody, UnifsIn = [Id=NewId | UnifsOut]],
            true, PrologBody),
      Body = (
         { PrologBody },
         RRightNodes
      ),
      (  comma_list(Guard, LeftOptions)
      -> HeadGuard = (Head, Guard)
      ;  HeadGuard = Head
      )
   },
   assert_rule(HeadGuard ==> Body),
   default_clause(Head).
compile_iter_nodes(Nodes, Name, Pat, Pats, Id, LeftOptions, Right, RightOptions, Body) -->
   {
      same_length(Pats, Pats_),
      append(Pats_, [UnifsIn, UnifsOut], Args),
      Head =.. [Name, [H|T], Node_, Index | Args],
      atom_concat(Name, '_', NewName),
      append(Pats_, [UnifsIn, UnifsTmp], SubSubArgs),
      SubSubCall =.. [NewName, H, Node_, Index | SubSubArgs],
      append(Pats_, [UnifsTmp, UnifsOut], SubArgs),
      SubCall =.. [Name, T, Node_, Index | SubArgs]
   },
   assert_rule(Head ==> (SubSubCall, SubCall)),
   default_clause(Head, []),
   compile_nodes(Nodes, NewName, Pat, Pats, Id, LeftOptions, Right, RightOptions, Body).

default_clause(Head) -->
   default_clause(Head, _).
default_clause(Head, DefaultArg) -->
   {
      Head =.. [Name | Args],
      Args = [Arg | _],
      (  subsumes_term([_|_], Arg)
      -> DefaultArg = []
      ;  true
      ),
      same_length(Args, DefaultArgs),
      nth0(0, DefaultArgs, DefaultArg),
      once(append(_, [In, Out], DefaultArgs)),
      DefaultHead =.. [Name | DefaultArgs]
   },
   assert_rule(DefaultHead ==> {Out = In}).

assert_rule(Rule) -->
   {expand_term(Rule, Term)},
   [Term].

term_nodes(T-Id, Nodes) :-
   phrase(term_nodes(T-Id), Nodes).
term_nodes(T-Id), compound(T) ==>
   [Node-node(Id, _Cost)],
   {  T =.. [F | Args],
      pairs_keys_values(Pairs, Args, Ids)
   },
   sequence(term_nodes, Pairs),
   { Node =.. [F | Ids] }.
term_nodes(T-Id), var(T) ==> {T = Id}.
term_nodes(T-Id) ==>
   [T-node(Id, _Cost)].

user:term_expansion(egraph:rewrite(Name, A, B), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, []) :- true), Clauses).
user:term_expansion(egraph:rewrite(Name, A, B, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, BOpt) :- true), Clauses).
user:term_expansion(egraph:rewrite(Name, A, AOpt, B, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, B, BOpt) :- true), Clauses).
user:term_expansion((egraph:rewrite(Name, A, AOpt, B, BOpt) :- Body), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, B, BOpt) :- Body), Clauses).
