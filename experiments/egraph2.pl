:- module(egraph, []).
:- use_module(library(rbtrees)).
:- use_module(library(dcg/high_order)).

M.empty() := EGraph :-
   rb_new(Nodes), rb_new(Parents), rb_new(UsedBy),
   ( nonvar(M) -> M = egraph(Next0, _, _, _, _) ; Next0 = 0 ),
   EGraph = egraph(Next0, Nodes, Parents, UsedBy, []).

M.next() := Id :-
   arg(1, M, Next0),
   Id is Next0 + 1,
   nb_setarg(1, M, Id).

M.add(Term) := EGraph :-
   add(Term, _, M, EGraph).
M.add(Term, ClassId) := EGraph :-
   (  compound(Term)
   -> Term =.. [F | Args],
      foldl(add, Args, ClassIds, M, M1),
      Node =.. [F | ClassIds],
      add_node(Node, ClassId, ClassIds, M1, EGraph)
   ;  add_node(Term, ClassId, [], M, EGraph)
   ).

M.add_node(Node, RootId, ArgsIds) := EGraph :-
   arg(2, M, Nodes0),
   (  rb_lookup(Node, ClassId, Nodes0)
   -> find(ClassId, RootId, M, EGraph)
   ;  next(M, ClassId),
      rb_insert_new(Nodes0, Node, ClassId, Nodes),
      arg(4, M, UsedBy0),
      rb_insert_new(UsedBy0, ClassId, [], UsedBy1),
      RootId = ClassId,
      arg(3, M, Parents0),
      rb_insert_new(Parents0, ClassId, RootId, Parents),
      foldl(used_by(Node), ArgsIds, UsedBy1, UsedBy),
      arg(1, M, Next1),
      arg(5, M, Worklist),
      EGraph = egraph(Next1, Nodes, Parents, UsedBy, Worklist)
   ).

used_by(Node, ClassId, In, Out) :-
   rb_update(In, ClassId, Set1, Set2, Out),
   ord_add_element(Set1, Node, Set2).

M.find(ClassId, RootClassId) := EGraph :-
   arg(3, M, Parents0),
   rb_lookup(ClassId, ParentClassId, Parents0),
   (  ClassId == ParentClassId
   -> RootClassId = ClassId, EGraph = M
   ;  rb_update(Parents0, ClassId, RootClassId, Parents),
      arg(1, M, Next), arg(2, M, Nodes), arg(4, M, UsedBy), arg(5, M, Worklist),
      M1 = egraph(Next, Nodes, Parents, UsedBy, Worklist),
      find(ParentClassId, RootClassId, M1, EGraph)
   ).

M.union(ClassA, ClassB) := EGraph :-
   find(ClassA, RootA, M, M1),
   find(ClassB, RootB, M1, M2),
   (  RootA == RootB
   -> EGraph = M2
   ;  arg(3, M2, Parents0),
      rb_update(Parents0, RootA, RootB, Parents),
      arg(4, M2, UsedBy0),
      rb_delete(UsedBy0, RootA, SetA, UsedBy1),
      rb_update(UsedBy1, RootB, SetB, Set, UsedBy2),
      ord_union(SetA, SetB, Set),
      arg(5, M2, Worklist0),
      ord_union(Worklist0, Set, Worklist),
      arg(1, M2, Next), arg(2, M2, Nodes),
      EGraph = egraph(Next, Nodes, Parents, UsedBy2, Worklist)
   ).

M.pop(H) := EGraph :-
   M = egraph(Next, Nodes, Parents, UsedBy, [H|T]),
   EGraph = egraph(Next, Nodes, Parents, UsedBy, T).
M.rebuild() := EGraph :-
   (  pop(H, M, M1)
   -> rebuild_node(H, M1, M2),
      rebuild(M2, EGraph)
   ;  EGraph = M
   ).
M.rebuild_node(Node) := EGraph :-
   (  compound(Node)
   -> Node =.. [F | Args],
      foldl(find, Args, NewArgs, M, M1),
      (  Args == NewArgs
      -> EGraph = M1
      ;  NewNode =.. [F | NewArgs],
         arg(2, M1, Nodes1),
         rb_lookup(Node, ClassId, Nodes1),
         (  rb_lookup(NewNode, NewClassId, Nodes1)
         -> M2 = M1
         ;  add_node(NewNode, NewClassId, NewArgs, M1, M2)
         ),
         union(ClassId, NewClassId, M2, EGraph)
      )
   ;  EGraph = M
   ).

opt(Goal, In, Out) :-
   (  call(Goal, In, Out)
   -> true
   ;  Out = In
   ).
rules(Node-ClassId) -->
   opt(commutativity(Node-ClassId)),
   % opt(identity(Node-ClassId)),
   opt(associativity(Node-ClassId)),
   [].

M.commutativity((A+B)-ClassId) := EGraph :-
   find(A, A1, M, M0),
   find(B, B1, M0, M1),
   add_node(B1+A1, NewClassId, [B1, A1], M1, M2),
   union(ClassId, NewClassId, M2, EGraph).
M.identity((A+B)-ClassId) := EGraph :-
   arg(2, M, Nodes0),
   rb_lookup(0, ZeroClassId, Nodes0),
   find(ZeroClassId, A1, M, M0),
   find(A, A1, M0, M1),
   find(B, B1, M1, M2),
   union(ClassId, B1, M2, EGraph).
M.associativity((A+BC)-ClassId) := EGraph :-
   debug(associativity, "BC:~p", [BC]),
   arg(2, M, Nodes0),
   rb_in(B+C, BC, Nodes0),
   debug(associativity, "BC:~p", [BC]),
   % M1 = M.find(BC_, BCId).find(BC, BCId),
   % debug(associativity, "BCId:~p", [BCId]),
   find(A, A1, M, M0),
   find(B, B1, M0, M1),
   find(C, C1, M1, M2),
   add_node(A1+B1, AB, [A1, B1], M2, M3),
   add_node(AB+C1, NewClassId, [AB, C1], M3, M4),
   union(ClassId, NewClassId, M4, EGraph).

M.match() := EGraph :-
   arg(2, M, Nodes0),
   rb_fold(rules, Nodes0, M, EGraph).
M.saturate() := EGraph :-
   saturate(inf, M, EGraph).
M.saturate(N) := EGraph :-
   (  N > 0
   -> match(M, M1),
      (  M1 == M
      -> EGraph = M
      ;  (  N == inf -> N1 = inf ; N1 is N - 1 ),
         rebuild(M1, M2),
         saturate(N1, M2, EGraph)
      )
   ;  EGraph = M
   ).

M.print() := M :-
   arg(2, M, Nodes0),
   rb_visit(Nodes0, Pairs),
   pairs_keys_values(Pairs, Nodes, ClassIds),
   foldl(find, ClassIds, ParentIds, M, _),
   pairs_keys_values(Pairs2, ParentIds, Nodes),
   keysort(Pairs2, Pairs3),
   group_pairs_by_key(Pairs3, Groups),
   print_term(Groups, []), nl.

M.basic_print() := M :-
   arg(2, M, Nodes0),   rb_visit(Nodes0, Nodes),
   format("Nodes: "),   print_term(Nodes, []), nl,
   arg(3, M, Parents0), rb_visit(Parents0, Parents),
   format("Parents: "), print_term(Parents, []), nl,
   arg(4, M, UsedBy0),  rb_visit(UsedBy0, UsedBy),
   format("UsedBy: "),  print_term(UsedBy, []), nl,
   arg(5, M, Worklist),
   format("Worklist: ~p~n", [Worklist]).

main(EGraph) :-
   empty(M0, M1),
   add(f(f(a)), FFA, M1, M2),
   add(a, A, M2, M3),
   union(FFA, A, M3, M4),
   add(f(f(f(f(a)))), _FFFFA, M4, M5),
   rebuild(M5, EGraph).
