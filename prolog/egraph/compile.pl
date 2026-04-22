:- module(egraph_compile, []).

/** <module> E-graph rewrite rule compiler

This module provides the term expansion infrastructure for compiling
declarative E-graph rewrite rules into efficient DCG predicates. 
These compiled predicates operate directly on the E-graph state during
saturation.

Rewrite rules are declared using the following forms, which are automatically
compiled via term expansion:

  * `egraph:rewrite(Name, Lhs, Rhs)`
  * `egraph:rewrite(Name, Lhs, Rhs, RhsOptions)`
  * `egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions)`
  * `egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions) :- Body`
  * `egraph:analyze(Name, Lhs, RhsOptions)`
  * `egraph:analyze(Name, Lhs, LhsOptions, RhsOptions)`
  * `egraph:analyze(Name, Lhs, LhsOptions, RhsOptions) :- Body`
  * `egraph:merge_property(Name, V1, V2, Merged)`
  * `egraph:merge_property(Name, V1, V2, Merged) :- Body`

Arguments:
  * `Name`: The atom used to identify and apply the rule. This name should be unique across all rules.
  * `Lhs`: The left-hand side pattern to match in the E-graph.
  * `Rhs`: The right-hand side pattern to insert into the E-graph.
  * `LhsOptions`: A list of conditions for the matched nodes. Options include:
    * `const(Var, Value)`: Matches only if the e-class `Var` represents the constant `Value`.
  * `RhsOptions`: A list of attributes for the newly created nodes. Options include:
    * `const(Value)`: Mark `Value` as a constant to the corresponding new e-class.
    * `cost(Cost)`: Sets a custom structural cost for the inserted `Rhs` root node.
  * `Body`: An optional Prolog body executed during the rewrite, typically used to evaluate arbitrary conditions or compute values for `Rhs` attributes.

Pattern Interpretation:
Patterns are written exactly as standard Prolog terms, mirroring how terms are added via `add_term//2`:
  * Literals (atoms, numbers, strings) match exact atomic values (e.g., `0` in `A + 0`, or `"foo"` in `g("foo")`).
  * Compound terms match the exact structural shape of complex terms in the E-graph (e.g., `A * (B + C)` or `f(X, Y)`).
  * Prolog variables act as wildcards matching any arbitrary subterm (e.g., `A` in `A + B`).
*/

:- use_module(library(dcg/high_order)).
:- use_module(library(debug)).
:- use_module('../egraph.pl', [lookup/2]).

compile(merge_property(Name, V1, V2, Merged) :- Body) -->
   [(
      Name:attr_unify_hook(V1, Y) :-
         (  get_attr(Y, Name, V2)
         -> Body,
            (  Merged \== V2
            -> put_attr(Y, Name, Merged),
               b_setval(egraph_changed, true)
            ;  Merged \== V1
            -> b_setval(egraph_changed, true)
            ;  true
            )
         ;  var(Y)
         -> put_attr(Y, Name, V1),
            b_setval(egraph_changed, true)
         ;  true
         )
   )].
compile(rewrite(Name, Left, LeftOptions, Right, RightOptions) :- Body) -->
   {  term_nodes(Left-Id, LeftNodes),
      LeftNodes = [Pat-_ | T],
      right_nodes(Right-RightId, RightNodes, Left-LeftNodes),
      maplist(expand_prop, LeftOptions, LeftExpanded)
   },
   compile_nodes(T, Name, Pat, [], Id, LeftExpanded, RightNodes, RightOptions, RightId, Body).

expand_prop(Prop, Expanded), Prop =.. [Name, Id, Value] =>
   Expanded = get_attr(Id, Name, Value).

common_variables(A, B) :-
   term_variables(A, VAs),
   term_variables(B, VBs),
   list_to_ord_set(VAs, ASet),
   list_to_ord_set(VBs, BSet),
   ord_intersect(ASet, BSet).

compile_nodes([NextPat-node(NextId, _) | Nodes], Name, Pat, Pats, Id, LeftOptions, Right, RightOptions, RightId, SubBody) ==>
   {
      append(Pats, [UnifsIn, UnifsOut], Args),
      Head =.. [Name, Pat, Id, Index | Args],
      atom_concat(Name, '_', NewName),
      partition(common_variables(Pat), LeftOptions, GuardList, LeftRest),
      append([Pat | GuardList], Pats, AllPats),
      append(AllPats, [UnifsIn, UnifsOut], SubCallArgs),
      SubCall =.. [NewName, NextIdNodes, Id, Index | SubCallArgs],
      Body = (
         {rb_lookup(NextId, NextIdNodes, Index)},
         SubCall
      ),
      (  comma_list(Guard, GuardList)
      -> HeadGuard = (Head, Guard)
      ;  HeadGuard = Head
      )
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
      maplist(collect_attrs(RightNodes), RightRest, ConstAttrs),
      
      (  comma_list(RightBody, ConstAttrs)
      -> true
      ;  RightBody = true
      ),
      mkconj(RightBody, UnifsIn = [Id=RightId | UnifsOut], PrologBody),
      Body = (
         { PrologBody },
         RightNodes
      ),
      (  comma_list(GuardOpts, LeftOptions)
      -> mkconj(GuardOpts, SubBody, Guard)
      ;  Guard = SubBody
      ),
      (  Guard == true
      -> HeadGuard = Head
      ;  HeadGuard = (Head, Guard)
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
term_nodes('$NODE'(Node)-Id) ==>
   [Node-node(Id, _Cost)].
term_nodes(T-Id), is_dict(T) ==>
   [Node-node(Id, _Cost)],
   {
      dict_pairs(T, Tag, Pairs),
      pairs_keys_values(Pairs, Keys, Values),
      pairs_keys_values(NodePairs, Keys, Ids),
      dict_create(Node, Tag, NodePairs),
      pairs_keys_values(SubPairs, Values, Ids)
   },
   sequence(term_nodes, SubPairs).
term_nodes(T-Id), compound(T) ==>
   [Node-node(Id, _Cost)],
   { pairs_args(T, Node, Pairs) },
   sequence(term_nodes, Pairs).
term_nodes(T-Id), var(T) ==> {T = Id}.
term_nodes(T-Id) ==>
   [T-node(Id, _Cost)].

right_nodes(T-Id, Nodes, Left-LeftNodes) :-
   keysort(LeftNodes, SortedLeftNodes),
   phrase(right_nodes(Left-SortedLeftNodes, T-Id), Nodes).
right_nodes(LeftNodes, '$NODE'(Node)-Id) ==>
   add_right_node(Node, Id, LeftNodes).
right_nodes(LeftNodes, T-Id), is_dict(T) ==>
   {
      dict_pairs(T, Tag, Pairs),
      pairs_keys_values(Pairs, Keys, Values),
      pairs_keys_values(NodePairs, Keys, Ids),
      dict_create(Node, Tag, NodePairs),
      pairs_keys_values(SubPairs, Values, Ids)
   },
   sequence(right_nodes(LeftNodes), SubPairs),
   add_right_node(Node, Id, LeftNodes).
right_nodes(LeftNodes, T-Id), compound(T) ==>
   { pairs_args(T, Node, Pairs) },
   sequence(right_nodes(LeftNodes), Pairs),
   add_right_node(Node, Id, LeftNodes).
right_nodes(LeftNodes, T-Id) ==>
   add_right_node(T, Id, LeftNodes).

add_right_node(Node, Id, Left-LeftNodes) -->
   (  { lookup(Node-node(_, _), LeftNodes) }
   -> [Node-node(Id, _Cost)]
   ;  { var(Node), contains_var(Node, Left) }
   -> { Node = Id }
   ;  [Node-node(Id, _Cost)]
   ).
   
pairs_args(T1, T2, Pairs) :-
   T1 =.. [F | Args],
   pairs_keys_values(Pairs, Args, Ids),
   T2 =.. [F | Ids].

collect_attrs(RightNodes, Prop, R), Prop =.. [Name, Value] =>
   (  lookup(Value-node(Id, _), RightNodes)
   -> R = put_attr(Id, Name, Value)
   ;  existence_error(rhs_node, Value)
   ).
collect_attrs(_, Prop, R), Prop =.. [Name, Id, Value] =>
   R = put_attr(Id, Name, Value).

debug_clauses(Clauses) :-
   (  debugging(egraph_compile)
   -> maplist(portray_clause(user_error), Clauses),
      nl(user_error)
   ;  true
   ).

user:term_expansion(egraph:merge_property(Name, V1, V2, Merged), Clauses) :-
   phrase(compile(merge_property(Name, V1, V2, Merged) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:merge_property(Name, V1, V2, Merged) :- Body), Clauses) :-
   phrase(compile(merge_property(Name, V1, V2, Merged) :- Body), Clauses),
   debug_clauses(Clauses).

user:term_expansion(egraph:analyze(Name, A, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, [], A, BOpt) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:analyze(Name, A, BOpt) :- Body), Clauses) :-
   phrase(compile(rewrite(Name, A, [], A, BOpt) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:analyze(Name, A, AOpt, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, A, BOpt) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:analyze(Name, A, AOpt, BOpt) :- Body), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, A, BOpt) :- Body), Clauses),
   debug_clauses(Clauses).

user:term_expansion(egraph:rewrite(Name, A, B), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, []) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rewrite(Name, A, B) :- Body), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, []) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:rewrite(Name, A, B, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, [], B, BOpt) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:rewrite(Name, A, AOpt, B, BOpt), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, B, BOpt) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rewrite(Name, A, AOpt, B, BOpt) :- Body), Clauses) :-
   phrase(compile(rewrite(Name, A, AOpt, B, BOpt) :- Body), Clauses),
   debug_clauses(Clauses).
