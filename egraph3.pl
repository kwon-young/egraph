% this is an egraph implementation in swi-prolog
% it uses prolog variables for class ids and ordset to store the list of nodes
% note the custom predicate lookup to search nodes by key only
% note the compilation of rewrite rules to dynamic predicate rule/2 to efficiently retrieve rules compatible with a node
% Please improve your code formatting when answering


:- use_module(library(dcg/high_order)).
:- use_module(library(ordsets)).
:- use_module(library(rbtrees)).

lookup(Item-V, [X1-V1, X2-V2, X3-V3, X4-V4|Xs]) :-
   !,
   compare(R4, Item, X4),
   (   R4=(>)
   ->  lookup(Item-V, Xs)
   ;   R4=(<)
   ->  compare(R2, Item, X2),
      (   R2=(>)
      ->  Item==X3, V = V3
      ;   R2=(<)
      ->  Item==X1, V = V1
      ;   V = V2
      )
   ;   V = V4
   ).
lookup(Item-V, [X1-V1, X2-V2|Xs]) :-
   !,
   compare(R2, Item, X2),
   (   R2=(>)
   ->  lookup(Item-V, Xs)
   ;   R2=(<)
   ->  Item==X1, V = V1
   ;   V = V2
   ).
lookup(Item-V, [X1-V1]) :-
   Item==X1, V = V1.

add(Term, Id, In, Out) :-
   (  compound(Term)
   -> Term =.. [F | Args],
      foldl(add, Args, Ids, In, Tmp),
      Node =.. [F | Ids],
      add_node(Node, Id, Tmp, Out)
   ;  add_node(Term, Id, In, Out)
   ).

add_node(Node-Id, In, Out) :-
   add_node(Node, Id, In, Out).
add_node(Node, Id, In, Out) :-
   (  lookup(Node-Id, In)
   -> Out = In
   ;  ord_add_element(In, Node-Id, Out)
   ).

union(A, B, In, Out) :-
   A = B,
   merge_nodes(In, Out).

merge_nodes(In, Out) :-
   sort(In, Sort),
   group_pairs_by_key(Sort, Groups),
   (  foldl(merge_group, Groups, Tmp, false, true)
   -> merge_nodes(Tmp, Out)
   ;  Sort = Out
   ).
merge_group(Node-[H | T], Node-H, In, Out) :-
   maplist(=(H), T),
   (  T == []
   -> Out = In
   ;  Out = true
   ).

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
      ord_del_element(Set1, RightId, Set2)
   },
   nodes_rule([Node], Pat, Left, Index, Right, Set2, LeftId=RightId).

rule_node([Node-Id | Left], G-Index, Right, RuleVars, Unif) -->
   { rb_lookup(Id, Nodes, Index) },
   nodes_rule(Nodes, Node, Left, G-Index, Right, RuleVars, Unif).
rule_node([], G-_Index, Right, _, Unif) -->
   Right, [Unif].

nodes_rule([Node | Nodes], Pat, Left, G-Index, Right, RuleVars, Unif) -->
   {copy_term(RuleVars, Pat-Left-Right, CRuleVars, CPat-CLeft-CRight)},
   (  {  Node = CPat,
         term_variables(Node, NodeVars),
         foldl([NodeVar, In, Out]>>exclude(==(NodeVar), In, Out), NodeVars, CRuleVars, C2RuleVars),
         Node = A+B
      },
      rule_node(CLeft, G-Index, CRight, C2RuleVars, Unif)
   -> []
   ;  []
   ),
   nodes_rule(Nodes, Pat, Left, G-Index, Right, RuleVars, Unif),
   [].
nodes_rule([], _Node, _Left, _Index, _Right, _, _Unif) -->
   [].

% A+B => B+A
% A+B-Id => B+A-Id
comm((A+B)-AB, _Nodes) -->
   !,
   [B+A-BA, AB=BA].
comm(_, _) --> [].

% A+(B+C) => (A+B)+C
% A+BC-ABC, B+C-BC => A+B-AB, AB+C-ABC
assoc((A+BC)-ABC, Index) -->
   !,
   {rb_lookup(BC, Nodes, Index)},
   assoc_(Nodes, A, ABC).
assoc(_, _) --> [].
assoc_([Node | Nodes], A, ABC) -->
   (  { Node = (B+C) }
   -> [A+B-AB, AB+C-ABC_, ABC=ABC_]
   ;  []
   ),
   assoc_(Nodes, A, ABC).
assoc_([], _, _) --> [].

rules(Index, Node) -->
   comm(Node, Index),
   assoc(Node, Index).

make_index(In, Index) :-
   transpose_pairs(In, Pairs),
   group_pairs_by_key(Pairs, Groups),
   ord_list_to_rbtree(Groups, Index).

match(Worklist, Index, Matches) :-
   % foldl(rules(Index), Worklist, Matches, []).
   phrase(sequence(node_rules(Index), Worklist), Matches, []).
push_back(L), L --> [].
rebuild(Matches) -->
   { exclude(unif, Matches, NewNodes) },
   push_back(NewNodes),
   merge_nodes.
saturate(N, In, Out) :-
   (  N > 0
   -> make_index(In, Index),
      match(In, In-Index, Matches),
      rebuild(Matches, In, Tmp),
      make_index(Tmp, Index_),
      pairs_keys_values(Tmp, Nodes_, Ids_),
      term_variables(Nodes_, Vars_),
      forall(member(V_, Vars_),
         (  rb_lookup(V_, _, Index_)
         -> true
         ;  gtrace
         )
      ),
      length(In, Len1),
      length(Tmp, Len2),
      print_term([Len1-Len2], []), nl,
      (  Len1 < Len2
      -> (  N == inf
         -> N1 = N
         ;  N1 is N - 1
         ),
         saturate(N1, Tmp, Out)
      ;  Len1 > Len2
      -> Out = Tmp
      ;  Out = Tmp
      )
   ;  Out = In
   ).

unif(A=B) :- A=B.

extract(Nodes, Nodes) :-
   transpose_pairs(Nodes, Pairs),
   group_pairs_by_key(Pairs, Groups),
   maplist([Id-L]>>member(Id, L), Groups).

% main -->
%    add(a, A),
%    add(f(f(a)), FFA),
%    union(A, FFA),
%    add(f(f(f(f(a)))), _FFFFA).



main(N, Var, G) :-
   retractall(rule(_, _)),
   Rules = [
      A+B => B+A,
      (A+B)+C => A+(B+C)
   ],
   maplist(compile_rule, Rules),
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

add_expr(N, Add) :-
   numlist(1, N, L), L = [H|T], foldl([B, A, A+B]>>true, T, H, Add).

:- begin_tests(node_rule).

test(sharing) :-
   phrase((
      add(b+c, BC),
      add(c+b, CB),
      union(BC, CB),
      add(a+(b+c), ABC)
   ), [], G),
   compile_rule(X+(Y+Z) => (X+Y)+Z, Key, Rule),
   last(G, Node),
   make_index(G, Index1),
   rb_visit(Index1, Pairs1),
   % print_term([graph-G, index-Pairs1, rule-Rule], []), nl,
   % extract(G, _),
   make_index(G, Index),
   phrase(node_rule(Node, G-Index, Rule), Match),
   rb_visit(Index, Pairs),
   % print_term([graph-G, index-Pairs, match-Match, rule-Rule, ABC], []), nl,
   rebuild(Match, G, G1),
   make_index(G, Index2),
   rb_visit(Index2, Pairs2),
   % extract(G1, _),
   length(G1, N1),
   % print_term([graph-N1-G1, index-Pairs2, match-Match, ABC], []), nl,
   fail.



:- end_tests(node_rule).
