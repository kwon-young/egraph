:- module(egraph_compile, []).

:- use_module(library(dcg/high_order)).
:- use_module('../egraph.pl', [lookup/2]).

compile(rewrite(Name, Left, LeftOptions, Right, RightOptions) :- Body) -->
   {  term_nodes(Left-Id, LeftNodes),
      LeftNodes = [Pat-_ | T],
      right_nodes(Right-RightId, RightNodes, Left-LeftNodes)
   },
   compile_nodes(T, Name, Pat, [], Id, LeftOptions, RightNodes, RightOptions, RightId, Body).

common_variables(A, B) :-
   term_variables(A, VAs),
   term_variables(B, VBs),
   list_to_ord_set(VAs, ASet),
   list_to_ord_set(VBs, BSet),
   ord_intersect(ASet, BSet).

compile_nodes([NextPat-node(NextId, _) | Nodes], Name, Pat, Pats, Id, LeftOptions, Right, RightOptions, RightId, SubBody) ==>
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
   compile_iter_nodes(Nodes, NewName, NextPat, AllPats, Id, LeftRest, Right, RightOptions, RightId, SubBody).
compile_nodes([], Name, Pat, Pats, Id, LeftOptions, RightNodes, RightOptions, RightId, SubBody) ==>
   {
      append(Pats, [UnifsIn, UnifsOut], Args),
      Head =.. [Name, Pat, Id, _Index | Args],
      (  last(RightNodes, _-node(_LastId, Cost))
      -> select_option(cost(Cost), RightOptions, RightRest, 1)
      ;  RightRest = RightOptions
      ),
      convlist([_-node(_, 1), _]>>true, RightNodes, _),
      (  comma_list(RightBody, RightRest)
      -> true
      ;  RightBody = true
      ),
      foldl(mkconj, [SubBody, RightBody, UnifsIn = [Id=RightId | UnifsOut]],
            true, PrologBody),
      Body = (
         { PrologBody },
         RightNodes
      ),
      (  comma_list(Guard, LeftOptions)
      -> HeadGuard = (Head, Guard)
      ;  HeadGuard = Head
      )
   },
   assert_rule(HeadGuard ==> Body),
   default_clause(Head).
compile_iter_nodes(Nodes, Name, Pat, Pats, Id, LeftOptions, Right, RightOptions, RightId, Body) -->
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
   compile_nodes(Nodes, NewName, Pat, Pats, Id, LeftOptions, Right, RightOptions, RightId, Body).

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
   { pairs_args(T, Node, Pairs) },
   sequence(term_nodes, Pairs).
term_nodes(T-Id), var(T) ==> {T = Id}.
term_nodes(T-Id) ==>
   [T-node(Id, _Cost)].

right_nodes(T-Id, Nodes, LeftNodes) :-
   phrase(right_nodes(LeftNodes, T-Id), Nodes).
right_nodes(LeftNodes, T-Id), compound(T) ==>
   { pairs_args(T, Node, Pairs) },
   sequence(right_nodes(LeftNodes), Pairs),
   add_right_node(Node, Id, LeftNodes).
right_nodes(LeftNodes, T-Id) ==>
   add_right_node(T, Id, LeftNodes).

add_right_node(Node, Id, Left-LeftNodes) -->
   (  { lookup(Node-node(Id, _), LeftNodes) }
   -> []
   ;  { var(Node), contains_var(Node, Left) }
   -> { Node = Id }
   ;  [Node-node(Id, _Cost)]
   ).
   
pairs_args(T1, T2, Pairs) :-
   T1 =.. [F | Args],
   pairs_keys_values(Pairs, Args, Ids),
   T2 =.. [F | Ids].


user:term_expansion(egraph:rewrite(Name, A, B), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, []) :- true), Clauses).
user:term_expansion(egraph:rewrite(Name, A, B, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, BOpt) :- true), Clauses).
user:term_expansion(egraph:rewrite(Name, A, AOpt, B, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, B, BOpt) :- true), Clauses).
user:term_expansion((egraph:rewrite(Name, A, AOpt, B, BOpt) :- Body), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, B, BOpt) :- Body), Clauses).
