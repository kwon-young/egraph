
compile_term(Var, Id), var(Var) ==>
   { Var = Id }.
compile_term(Term, Id) ==>
   (  { compound(Term) }
   -> {  Term =.. [F | Args],
         pairs_keys_values(Pairs, Args, Ids),
         Node =.. [F | Ids]
      },
      sequence(compile_pair, Pairs)
   ;  { Node = Term }
   ),
   add_node_(Node, Id).

add_node_(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  Out = [Node-Id | In]
   ).
compile_pair(Term-Id) -->
   compile_term(Term, Id).

:- dynamic rule/2.

lookup_([Node-Id | L], Node_-Id_) :-
   (  Node == Node_
   -> Id = Id_
   ;  lookup_(L, Node_-Id_)
   ).

compile_rules(Rules) :-
   retractall(rule(_, _)),
   maplist(compile_rule, Rules).
compile_rule(Left => Right, Key, Rule) :-
   phrase(compile_term(Left, LeftId), [], LeftNodes),
   LeftNodes = [Key_-_|_],
   copy_term(Key_, Key),
   phrase(compile_term(Right, RightId), [], RightNodes_),
   exclude(lookup_(LeftNodes), RightNodes_, RightNodes),
   reverse(RightNodes, RRightNodes),
   Rule = (LeftId-LeftNodes => RightId-RRightNodes).
compile_rule(Term) :-
   compile_rule(Term, Key, Rule),
   (  rule(Key, Rule)
   -> true
   ;  assertz(rule(Key, Rule))
   ).

node_rules(Index, Node) -->
   {  Node = Key-_,
      findall(Rule, rule(Key, Rule), Rules)
   },
   sequence(node_rule(Node, Index), Rules).

node_rule(Node-Id, Index, LeftId-[Pat-Id | Left] => RightId-Right) -->
   {  term_variables(Pat-Left-Right, Vars),
      list_to_ord_set(Vars, Set1),
      % ord_del_element(Set1, RightId, Set2)
      exclude(==(RightId), Set1, Set2)
   },
   nodes_rule([Node], Pat, Left, Index, Right, Set2, LeftId=RightId).

rule_node([Node-Id | Left], G-Index, Right, RuleVars, Unif) -->
   { rb_lookup(Id, Nodes, Index) },
   nodes_rule(Nodes, Node, Left, G-Index, Right, RuleVars, Unif).
rule_node([], _Index, Right, _, Unif) -->
   Right, [Unif].

nodes_rule([Node | Nodes], Pat, Left, G-Index, Right, RuleVars, Unif) -->
   {copy_term(RuleVars, Pat-Left-Right, CRuleVars, CPat-CLeft-CRight)},
   (  {  Node =@= CPat, Node = CPat,
         term_variables(Node, NodeVars),
         foldl([NodeVar, In, Out]>>exclude(==(NodeVar), In, Out), NodeVars, CRuleVars, C2RuleVars)
         % Node = A+B
      },
      rule_node(CLeft, G-Index, CRight, C2RuleVars, Unif)
   -> []
   ;  []
   ),
   nodes_rule(Nodes, Pat, Left, G-Index, Right, RuleVars, Unif),
   [].
nodes_rule([], _Node, _Left, _Index, _Right, _, _Unif) -->
   [].

main(N, Var, G) :-
   Rules = [
      A+B => B+A,
      (A+B)+C => A+(B+C)
   ],
   compile_rules(Rules),
   N1 is N - 1,
   numlist(0, N1, [H|T]),
   foldl([B, A, A+B]>>true, T, H, Add),
   time(phrase(example(N, Add, Var), [], G)),
   length(G, Num1),
   Num is 3**(N) - 2**(N+1) + 1 + N,
   format("~p ~p~n", [Num, Num1]).
example(N, Term, Var) -->
   add(Term, Var),
   saturate(inf),
   % extract.
   [].
