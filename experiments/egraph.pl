:- module(egraph, []).
:- use_module(library(rbtrees)).
:- use_module(library(dcg/high_order)).

M.empty() := EGraph :-
   rb_new(Nodes), rb_new(Parents), rb_new(UsedBy),
   EGraph = egraph{next: M.get(next, 0), nodes: Nodes, parents: Parents, used_by: UsedBy, worklist: []}.

M.next() := Id :-
   Id is M.next + 1,
   nb_set_dict(next, M, Id).

M.add(Term) := EGraph :-
   EGraph = M.add(Term, _).
M.add(Term, ClassId) := EGraph :-
   (  compound(Term)
   -> Term =.. [F | Args],
      foldl(add, Args, ClassIds, M, M1),
      Node =.. [F | ClassIds],
      EGraph = M1.add_node(Node, ClassId, ClassIds)
   ;  EGraph = M.add_node(Term, ClassId, [])
   ).

M.add_node(Node, RootId, ArgsIds) := EGraph :-
   (  rb_lookup(Node, ClassId, M.nodes)
   -> EGraph = M.find(ClassId, RootId)
   ;  ClassId = M.next(),
      rb_insert_new(M.nodes, Node, ClassId, Nodes),
      rb_insert_new(M.used_by, ClassId, [], UsedBy1),
      RootId = ClassId,
      rb_insert_new(M.parents, ClassId, RootId, Parents),
      foldl(used_by(Node), ArgsIds, UsedBy1, UsedBy),
      EGraph = M.put([nodes: Nodes, parents: Parents, used_by: UsedBy])
   ).

used_by(Node, ClassId, In, Out) :-
   rb_update(In, ClassId, Set1, Set2, Out),
   ord_add_element(Set1, Node, Set2).

M.find(ClassId, RootClassId) := EGraph :-
   rb_lookup(ClassId, ParentClassId, M.parents),
   (  ClassId == ParentClassId
   -> RootClassId = ClassId, M = EGraph
   ;  rb_update(M.parents, ClassId, RootClassId, Parents),
      M1 = M.put(parents, Parents),
      EGraph = M1.find(ParentClassId, RootClassId)
   ).

M.union(ClassA, ClassB) := EGraph :-
   M1 = M.find(ClassA, RootA),
   M2 = M1.find(ClassB, RootB),
   (  RootA == RootB
   -> EGraph = M2
   ;  rb_update(M2.parents, RootA, RootB, Parents),
      rb_delete(M2.used_by, RootA, SetA, UsedBy1),
      rb_update(UsedBy1, RootB, SetB, Set, UsedBy2),
      ord_union(SetA, SetB, Set),
      ord_union(M2.worklist, Set, Worklist),
      EGraph = M2.put([parents: Parents, used_by: UsedBy2, worklist: Worklist])
   ).

M.pop(H) := EGraph :-
   get_dict(worklist, M, [H | T], EGraph, T).
M.rebuild() := EGraph :-
   (  M1 = M.pop(H)
   -> M2 = M1.rebuild_node(H),
      EGraph = M2.rebuild()
   ;  EGraph = M
   ).
M.rebuild_node(Node) := EGraph :-
   (  compound(Node)
   -> Node =.. [F | Args],
      foldl(find, Args, NewArgs, M, M1),
      (  Args == NewArgs
      -> EGraph = M1
      ;  NewNode =.. [F | NewArgs],
         rb_lookup(Node, ClassId, M1.nodes),
         (  rb_lookup(NewNode, NewClassId, M1.nodes)
         -> M2 = M1
         ;  M2 = M1.add_node(NewNode, NewClassId, NewArgs)
         ),
         EGraph = M2.union(ClassId, NewClassId)
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
   M1 = M.find(A, A1).find(B, B1),
   EGraph = M1.add_node(B1+A1, NewClassId, [B1, A1]).union(ClassId, NewClassId).
M.identity((A+B)-ClassId) := EGraph :-
   rb_lookup(0, ZeroClassId, M.nodes),
   EGraph = M.find(ZeroClassId, A1).find(A, A1).find(B, B1).union(ClassId, B1).
M.associativity((A+BC)-ClassId) := EGraph :-
   debug(associativity, "BC:~p", [BC]),
   rb_in(B+C, BC, M.nodes),
   debug(associativity, "BC:~p", [BC]),
   % M1 = M.find(BC_, BCId).find(BC, BCId),
   % debug(associativity, "BCId:~p", [BCId]),
   M2 = M.find(A, A1).find(B, B1).find(C, C1),
   EGraph = M2.add_node(A1+B1, AB, [A1, B1]).add_node(AB+C1, NewClassId, [AB, C1]).union(ClassId, NewClassId).

M.match() := EGraph :-
   rb_fold(rules, M.nodes, M, EGraph).
M.saturate() := EGraph :-
   EGraph = M.saturate(inf).
M.saturate(N) := EGraph :-
   (  N > 0
   -> M1 = M.match(),
      (  M1 == M
      -> EGraph = M
      ;  (  N == inf
         -> N1 = inf
         ;  N1 is N - 1
         ),
         EGraph = M1.rebuild().saturate(N1)
      )
   ;  EGraph = M
   ).

M.print() := M :-
   rb_visit(M.nodes, Pairs),
   pairs_keys_values(Pairs, Nodes, ClassIds),
   foldl(find, ClassIds, ParentIds, M, _),
   pairs_keys_values(Pairs2, ParentIds, Nodes),
   keysort(Pairs2, Pairs3),
   group_pairs_by_key(Pairs3, Groups),
   print_term(Groups, []), nl.

M.basic_print() := M :-
   rb_visit(M.nodes, Nodes),
   format("Nodes: "), print_term(Nodes, []), nl,
   rb_visit(M.parents, Parents),
   format("Parents: "), print_term(Parents, []), nl,
   rb_visit(M.used_by, UsedBy),
   format("UsedBy: "), print_term(UsedBy, []), nl,
   format("Worklist: ~p~n", [M.worklist]).

main(EGraph) :-
   M1 = egraph{}.empty().add(f(f(a)), FFA),
   M2 = M1.add(a, A),
   M3 = M2.union(FFA, A),
   M4 = M3.add(f(f(f(f(a)))), _FFFFA),
   EGraph = M4.rebuild().
