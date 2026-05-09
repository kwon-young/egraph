:- module(egraph_compile, []).

/** <module> E-graph rule compiler
Provides a generalized rule compiler through term expansion.

Supported forms:
  * egraph:rewrite(Name, Lhs, Rhs)
  * egraph:rewrite(Name, Lhs, Rhs, RhsOptions)
  * egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions)
  * egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions) :- Body
  * egraph:analyze(Name, Lhs, RhsOptions)
  * egraph:analyze(Name, Lhs, LhsOptions, RhsOptions)
  * egraph:analyze(Name, Lhs, LhsOptions, RhsOptions) :- Body
  * egraph:merge_property(Name, V1, V2, Merged)
  * egraph:merge_property(Name, V1, V2, Merged) :- Body
  * egraph:rule(Name, Lhs, Rhs)
  * egraph:rule(Name, Lhs, Rhs) :- Body
  * egraph:rule(Name, Lhs, Rhs, RhsOptions)
  * egraph:rule(Name, Lhs, Rhs, RhsOptions) :- Body
  * egraph:rule(Name, Lhs, LhsOptions, Rhs, RhsOptions)
  * egraph:rule(Name, Lhs, LhsOptions, Rhs, RhsOptions) :- Body

For `egraph:rule/5`:
egraph:rule(Name, LhsPatterns, LhsOptions, RhsPatterns, RhsOptions) :- Body.

Where:
   * Patterns is a list of Pattern-Id pairs
   * shared class Ids between left and right patterns will be unified
   * Options is a list of properties compound: Name(Key, Value)
      * if Key is not a class id variable (like a subterm), Name can only be `cost`
      * compounds can be prefixed by `\+` to negate the lookup
      * left options will "get" the property
      * right options will "set" the property
   * Body must be free of class id variables contained in left and right patterns
**/

:- use_module(library(dcg/high_order)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(heaps)).
:- use_module('../egraph.pl', [add_terms//2]).

% 1. make implicit unification explicit
%    left class ids (value of the pairs) shared with right class ids are
%    implicit unification with different (keys of the pairs).
%    setting class property requires explicit unification from a fresh class id
%    shared right class ids should be copied and unification pairs added to Unifs
explicit_unifs(Lefts, Rights, RightOpts, RightsCopy, RightOptsCopy, AllUnifs) :-
   filter_unifs(Rights, RightsUnifs, Rights1),
   phrase(cross_class(Rights1, Rights2, Lefts), CrossUnifs),
   terms_class_ids(Lefts, LeftClassIds),
   terms_class_ids(Rights2, RightClassIds),
   phrase((
      product(shared_class, Lefts, Rights2),
      sequence(set_prop(LeftClassIds, RightClassIds), RightOpts)
   ), SharedClasses),
   sort(SharedClasses, SortedClasses),
   copy_term(SortedClasses, Rights2-RightOpts,
             RightClasses, RightsCopy-RightOptsCopy),
   maplist([A, B, A=B]>>true, SortedClasses, RightClasses, Unifs),
   append(RightsUnifs, Unifs, TempUnifs),
   append(TempUnifs, CrossUnifs, AllUnifs).

terms_class_ids(Terms, ClassIds) :-
   phrase((
      add_terms(Terms, [var(class)])
   ), [], Nodes),
   maplist(pair_classids, Nodes, ClassIdsList),
   append(ClassIdsList, ClassIdsUnsorted),
   sort(ClassIdsUnsorted, ClassIds).

filter_unifs([], Unifs, Rights) =>
   Unifs = [], Rights = [].
filter_unifs([A-B | RightNodes], Unifs, Rights), var(A), var(B) =>
   Unifs = [A=B | UnifsRest],
   filter_unifs(RightNodes, UnifsRest, Rights).
filter_unifs([RightNode | RightNodes], Unifs, Rights) =>
   Rights = [RightNode | RightsRest],
   filter_unifs(RightNodes, Unifs, RightsRest).
   
product(_, [], _) --> [].
product(Goal, [H | T], L) -->
   sequence(call(Goal, H), L),
   product(Goal, T, L).

cross_class([Right-RightClass | Rights], Rights1, Lefts),
      cross_class_(Lefts, Right-RightClass, LeftClass) ==>
   [LeftClass=RightClass],
   cross_class(Rights, Rights1, Lefts).
cross_class([Right | Rights], Rights1, Lefts) ==>
   { Rights1 = [Right | Rights2] },
   cross_class(Rights, Rights2, Lefts).
cross_class([], Rights, _) ==>
   { Rights = [] }.

cross_class_([Node-LeftClass | _], Node-RightClass, R), LeftClass \== RightClass =>
   R = LeftClass.
cross_class_([_ | Lefts], Right, R) =>
   cross_class_(Lefts, Right, R).
cross_class_([], _, _) => fail.

shared_class(LeftNode-Class, RightNode-Class), LeftNode \== RightNode ==>
   [Class].
shared_class(_, _) ==> [].

set_prop(LeftVars, _RightVars, Opt),
      Opt =.. [Name, Key, _],
      Name \== cost,
      var(Key),
      ord_memberchk(Key, LeftVars) ==>
   [Key].
set_prop(_LeftVars, RightVars, Opt),
      Opt =.. [Name, Key, _],
      Name \== cost,
      var(Key),
      ord_memberchk(Key, RightVars) ==>
   [].
set_prop(_, _, Opt), Opt =.. [Name, _, _], Name == cost ==> [].

optimal_order(Nodes, OutputVars, OptimalPlan) :-
   sort(Nodes, SortedNodes),
   empty_heap(EmptyHeap),
   add_to_heap(EmptyHeap, 0, state(SortedNodes, [], []), Heap),
   dijkstra(Heap, OutputVars, OptimalPlan).

dijkstra(Heap, OutputVars, OptimalPlan) :-
   get_from_heap(Heap, Cost, state(Remaining, BoundVars, Plan), Heap1),
   (  Remaining == []
   -> reverse(Plan, OptimalPlan)
   ;  expand_states(Remaining, Remaining, BoundVars, OutputVars, Plan, Cost, Heap1, Heap2),
      dijkstra(Heap2, OutputVars, OptimalPlan)
   ).

expand_states([], _Remaining, _BoundVars, _OutputVars, _Plan, _Cost, Heap, Heap).
expand_states([Node | Siblings], Remaining, BoundVars, OutputVars, Plan, Cost, HeapIn, HeapOut) :-
   ord_selectchk(Node, Remaining, NewRemaining),
   Node = Pat-_,
   pair_classids(Node, Vars),
   sort(Vars, SortedVars),
   step_cost(Pat, SortedVars, BoundVars, OutputVars, StepCost),
   NewCost is Cost + StepCost,
   ord_union(BoundVars, SortedVars, NewBoundVars),
   add_to_heap(HeapIn, NewCost, state(NewRemaining, NewBoundVars, [Node | Plan]), HeapMid),
   expand_states(Siblings, Remaining, BoundVars, OutputVars, Plan, Cost, HeapMid, HeapOut).

pair_classids(Pat-ClassInfo, Vars) :-
   (  var(Pat)
   -> term_variables(ClassInfo, Vars)
   ;  term_variables(Pat-ClassInfo, Vars)
   ).

step_cost(Pat, NodeVars, BoundVars, OutputVars, Cost) :-
   ord_subtract(NodeVars, BoundVars, UnboundVars),
   ord_intersection(UnboundVars, OutputVars, UnboundOutput),
   length(UnboundVars, NumUnbound),
   length(UnboundOutput, NumOutput),
   NumExistential is NumUnbound - NumOutput,
   (  var(Pat)
   -> PatCost = 10
   ;  PatCost = 0
   ),
   (  (BoundVars == [] ; ord_intersect(NodeVars, BoundVars))
   -> Cost is NumExistential * 2 + NumOutput + PatCost
   ;  Cost = 1000
   ).

expand_prop(F, \+ Prop, NotAttr) =>
   expand_prop(F, Prop, Attr),
   NotAttr = (\+ Attr).
expand_prop(F, Prop, Attr) =>
   Prop =.. [Name, Key, Value],
   Attr =.. [F, Key, Name, Value].

ord_term_variables(Term, SortedVars) :-
   term_variables(Term, Vars),
   sort(Vars, SortedVars).

common_vars(A, B, Common) :-
   ord_term_variables(A, AVars),
   ord_term_variables(B, BVars),
   ord_intersection(AVars, BVars, Common).

select_id_guards(_, [], Rest) ==> { Rest = [] }.
select_id_guards(Id, [get_attr(Id, Name, Value) | Guards], Rest) ==>
   [get_attr(Id, Name, Value)],
   select_id_guards(Id, Guards, Rest).
select_id_guards(Id, [\+ get_attr(Id, Name, Value) | Guards], Rest) ==>
   [\+ get_attr(Id, Name, Value)],
   select_id_guards(Id, Guards, Rest).
select_id_guards(Id, [Guard | Guards], GuardRest) ==>
   { GuardRest = [Guard | Rest] },
   select_id_guards(Id, Guards, Rest).
select_ids_guards([], Guards, Rest) --> { Rest = Guards }.
select_ids_guards([Id | Ids], Guards, Rest) -->
   select_id_guards(Id, Guards, R1),
   select_ids_guards(Ids, R1, Rest).

select_pat_guards(Pat, Guards, Rest), is_dict(Pat) ==>
   {  dict_pairs(Pat, _, Pairs),
      pairs_values(Pairs, Ids)
   },
   select_ids_guards(Ids, Guards, Rest).
select_pat_guards(Pat, Guards, Rest), compound(Pat) ==>
   { compound_name_arguments(Pat, _, Ids) },
   select_ids_guards(Ids, Guards, Rest).
select_pat_guards(_, Guards, Rest) ==> {Rest = Guards}.

select_guards(Pat-node(Id, _), Guards, Rest) -->
   select_id_guards(Id, Guards, R1),
   select_pat_guards(Pat, R1, Rest).

mask_args(_Order, _MinId, _Context, [], []).
mask_args(Order, MinId, Context, [Var | Vars], [Mask | Masks]) :-
   (  ord_memberchk(Var, Context)
   -> Mask = Var
   ;  Order == min
   -> Mask = MinId
   ;  Mask = max
   ),
   mask_args(Order, MinId, Context, Vars, Masks).

pat_min_max(MinId, Context, Pat, Min, Max), is_dict(Pat) =>
   dict_pairs(Pat, Tag, Pairs),
   pairs_keys_values(Pairs, Keys, Args),
   mask_args(min, MinId, Context, Args, MinArgs),
   mask_args(max, MinId, Context, Args, MaxArgs),
   pairs_keys_values(MinPairs, Keys, MinArgs),
   pairs_keys_values(MaxPairs, Keys, MaxArgs),
   dict_create(Min, Tag, MinPairs),
   dict_create(Max, Tag, MaxPairs).
pat_min_max(MinId, Context, Pat, Min, Max), compound(Pat) =>
   compound_name_arguments(Pat, Name, Args),
   mask_args(min, MinId, Context, Args, MinArgs),
   mask_args(max, MinId, Context, Args, MaxArgs),
   compound_name_arguments(Min, Name, MinArgs),
   compound_name_arguments(Max, Name, MaxArgs).
pat_min_max(_MinId, _Context, Pat, Min, Max) =>
   Min = Pat, Max = Pat.

node_min_max(MinId, Context, Pat-_, Min, Max) :-
   pat_min_max(MinId, Context, Pat, MinPat, MaxPat),
   Min = MinPat-_,
   Max = MaxPat-node(max, inf).

compile((merge_property(Name, V1, V2, Merged) :- Body)) -->
   [(
      Name:attr_unify_hook(V1, Y) :-
         (  get_attr(Y, Name, V2)
         -> Body,
            (  Merged \== V2
            -> put_attr(Y, Name, Merged),
               b_setval(egraph_changed, true)
            ;  true
            )
         ;  var(Y)
         -> put_attr(Y, Name, V1),
            b_setval(egraph_changed, true)
         ;  true
         )
   )].
compile((rule(Name, Lefts, LeftOpts, Rights, RightOpts) :- Body)) -->
   {  explicit_unifs(Lefts, Rights, RightOpts, Rights1, RightOpts1, Unifs),
      partition(=(cost(_, _)), LeftOpts, LeftCosts, LeftProps),
      partition(=(cost(_, _)), RightOpts1, RightCosts, RightProps),
      phrase(add_terms(Lefts, [var(class) | LeftCosts]), [], LeftNodes),
      phrase(add_terms(Rights1, [var(class), nodes(LeftNodes) | RightCosts]), [], RightNodes),
      % costs bindings are now inside the Nodes
      common_vars((RightNodes, RightProps, Body, Unifs), (LeftNodes, LeftProps), OutputVars),
      optimal_order(LeftNodes, OutputVars, QueryNodes),
      maplist(expand_prop(get_attr), LeftProps, LeftAttrs),
      maplist(expand_prop(put_attr), RightProps, RightAttrs),
      term_singletons((QueryNodes, LeftAttrs, RightNodes, RightAttrs, Body, Unifs), Singletons)
   },
   compile_nodes(QueryNodes, Name, '$empty'-node(_, 0), [], LeftAttrs, RightNodes, RightAttrs, Body, Unifs, Singletons).

compile_nodes([], Name, Pat, Context, LeftAttrs, RightNodes, RightAttrs, FinalBody, Unifs, _Singletons) ==>
   {  Head =.. [Name, Pat, state(Context, _EGraph, _Index, _Parents, _MinId), UnifsIn, UnifsOut],
      (  comma_list(LeftGuard, LeftAttrs)
      -> mkconj(LeftGuard, FinalBody, Guard)
      ;  Guard = FinalBody
      ),
      mkconj(Head, Guard, HeadGuard),
      (  comma_list(RightBody, RightAttrs)
      -> true
      ;  RightBody = true
      ),
      append(Unifs, UnifsOut, UnifsList),
      mkconj(RightBody, UnifsIn = UnifsList, PrologBody),
      Body = (
         { PrologBody },
         RightNodes
      )
   },
   assert_rule(HeadGuard ==> Body),
   default_clause(Head).
compile_nodes([NextPat-node(NextId, NextCost) | Rest], Name, Pat,
              Context, LeftAttrs, RightNodes, RightAttrs, FinalBody, Unifs, Singletons) ==>
   {  Head =.. [Name, Pat, state(Context, EGraph, Index, Parents, MinId), UnifsIn, UnifsOut],
      phrase(select_guards(Pat, LeftAttrs, LeftRest), GuardList),
      (  comma_list(Guard, GuardList)
      -> HeadGuard = (Head, Guard)
      ;  HeadGuard = Head
      ),
      ord_term_variables((Pat, GuardList), NewVars),
      ord_union(Context, NewVars, NewContext),
      term_variables(NextPat, NextPatVars),
      ord_intersection(NextPatVars, NewContext, ParentVars),
      ord_intersection([NextId], NewContext, ChildVars),
      (  ParentVars = [ParentVar | _]
      -> LookupList = [(rb_lookup(ParentVar, OutNodes, Parents) -> true ; OutNodes = [])]
      ;  ChildVars = [ChildVar | _]
      -> LookupList = [rb_lookup(ChildVar, OutNodes, Index)]
      ;  % Singletons can't be an ordlist as its variables are bound during compilation
         var(NextPat), contains_var(NextPat, Singletons)
      -> LookupList = [Index = t(_, OutNodes)], IsSingleton = true
      ;  LookupList = [], OutNodes = EGraph
      ),
      node_min_max(MinId, NewContext, NextPat-node(NextId, NextCost), Min, Max),
      (  comma_list(LookupCode, LookupList)
      -> true
      ;  LookupCode = true
      ),
      atom_concat(Name, '_', NewName),
      SubCall =.. [NewName, OutNodes, Min, Max, state(NewContext, EGraph, Index, Parents, MinId), UnifsIn, UnifsOut]
   },
   assert_rule((HeadGuard ==> ({LookupCode}, SubCall))),
   default_clause(Head),
   compile_iter_nodes(Rest, NewName, NextPat-node(NextId, NextCost), NewContext,
                      LeftRest, RightNodes, RightAttrs, FinalBody, Unifs, Singletons, IsSingleton).

compile_iter_nodes(Pats, Name, Pat-Node, Context, LeftRest, RightNodes,
                   RightAttrs, FinalBody, Unifs, Singletons, true) ==>
   {  Node = node(Id, _Cost),
      atom_concat(Name, '_', NewName),
      
      HeadEmpty =.. [Name, black('',_,_,_), _Min, _Max, _StateVar, UnifsIn, UnifsOut],
      
      HeadRed =.. [Name, red(L, Id, _, R), Min, Max, StateVar, UnifsIn, UnifsOut],
      HeadBlack =.. [Name, black(L, Id, _, R), Min, Max, StateVar, UnifsIn, UnifsOut],
      
      CallL =.. [Name, L, Min, Max, StateVar, UnifsIn, UnifsTmp1],
      SubCall =.. [NewName, Pat-node(Id, 1), StateVar, UnifsTmp1, UnifsTmp2],
      CallR =.. [Name, R, Min, Max, StateVar, UnifsTmp2, UnifsOut]
   },
   assert_rule((HeadEmpty ==> { UnifsOut = UnifsIn })),
   assert_rule((HeadRed ==> (CallL, SubCall, CallR))),
   assert_rule((HeadBlack ==> (CallL, SubCall, CallR))),
   compile_nodes(Pats, NewName, Pat-Node, Context, LeftRest, RightNodes,
                 RightAttrs, FinalBody, Unifs, Singletons).
compile_iter_nodes(Pats, Name, Pat-Node, Context, LeftRest, RightNodes,
                   RightAttrs, FinalBody, Unifs, Singletons, _), var(Pat) ==>
   {  Head =.. [Name, [H | T], Min, Max, StateVar, UnifsIn, UnifsOut],
      atom_concat(Name, '_', NewName),
      SubCall =.. [NewName, H, StateVar, UnifsIn, UnifsTmp],
      RecCall =.. [Name, T, Min, Max, StateVar, UnifsTmp, UnifsOut]
   },
   assert_rule((Head ==> (SubCall, RecCall))),
   default_clause(Head, []),
   compile_nodes(Pats, NewName, Pat-Node, Context, LeftRest, RightNodes,
                 RightAttrs, FinalBody, Unifs, Singletons).
compile_iter_nodes(Pats, Name, Pat, Context, LeftRest, RightNodes,
                   RightAttrs, FinalBody, Unifs, Singletons, _) ==>
   {  atom_concat(Name, '_take', TakeName),

      % --- Fast-Forward Predicate (Name) ---
      Head4Proto =.. [Name, [_X1, _X2, _X3, X4 | T], Min, Max, StateVar, UnifsIn, UnifsOut],
      Head4Guard = (Head4Proto, X4 @< Min),
      RecCall4   =.. [Name, T, Min, Max, StateVar, UnifsIn, UnifsOut],

      Head1Proto =.. [Name, [H | T], Min, Max, StateVar, UnifsIn, UnifsOut],
      Head1Guard = (Head1Proto, H @< Min),
      RecCall1   =.. [Name, T, Min, Max, StateVar, UnifsIn, UnifsOut],

      HeadFallProto =.. [Name, List, Min, Max, StateVar, UnifsIn, UnifsOut],
      TakeCall      =.. [TakeName, List, Max, StateVar, UnifsIn, UnifsOut],

      % --- Collection Predicate (TakeName) ---
      TakeStopProto =.. [TakeName, [H | _], Max, _StateVar, UnifsIn, UnifsOut],
      TakeStopGuard = (TakeStopProto, H @> Max),

      TakeProto =.. [TakeName, [H | T], Max, StateVar, UnifsIn, UnifsOut],

      atom_concat(Name, '_', NewName),
      SubCall =.. [NewName, H, StateVar, UnifsIn, UnifsTmp],
      RecTakeCall =.. [TakeName, T, Max, StateVar, UnifsTmp, UnifsOut]
   },
   % Fast-forward clauses
   assert_rule((Head4Guard ==> RecCall4)),
   assert_rule((Head1Guard ==> RecCall1)),
   assert_rule((HeadFallProto ==> TakeCall)),

   % Collection clauses
   assert_rule((TakeStopGuard ==> { UnifsOut = UnifsIn })),
   assert_rule((TakeProto ==> (SubCall, RecTakeCall))),
   default_clause(TakeProto, []),
   compile_nodes(Pats, NewName, Pat, Context, LeftRest, RightNodes,
                 RightAttrs, FinalBody, Unifs, Singletons).

default_clause(Head) -->
   default_clause(Head, _).
default_clause(Head, FirstArg) -->
   {  Head =.. [Name, Pat | ArgsRest],
      Args = [Pat | ArgsRest],
      same_length(Args, DefaultArgs),
      nth0(0, DefaultArgs, FirstArg),
      once(append(_, [In, Out], DefaultArgs)),
      DefaultHead =.. [Name | DefaultArgs]
   },
   assert_rule(DefaultHead ==> { Out = In }).

assert_rule(Rule) -->
   {expand_term(Rule, Term)},
   [Term].

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

standardize_option(Term, _Id, cost(Cost), R) => R = cost(Term, Cost).
standardize_option(Term, Id, \+ Opt, R) =>
   standardize_option(Term, Id, Opt, SubR),
   R = (\+ SubR).
standardize_option(_Term, Id, Opt, R), Opt =.. [Name, Value] => R =.. [Name, Id, Value].
standardize_option(_Term, _Id, Opt, R), Opt =.. [_Name, _Key, _Value] => R = Opt.

user:term_expansion((egraph:analyze(Name, Left, LeftOpts, RightOpts) :- Body), Clauses) :-
   maplist(standardize_option(Left, Id), LeftOpts, StdLeftOpts),
   maplist(standardize_option(Left, Id), RightOpts, StdRightOpts),
   phrase(compile(rule(Name, [Left-Id], StdLeftOpts, [], StdRightOpts) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:analyze(Name, Left, LeftOpts, RightOpts), Clauses) :-
   maplist(standardize_option(Left, Id), LeftOpts, StdLeftOpts),
   maplist(standardize_option(Left, Id), RightOpts, StdRightOpts),
   phrase(compile(rule(Name, [Left-Id], StdLeftOpts, [], StdRightOpts) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:analyze(Name, Left, RightOpts) :- Body), Clauses) :-
   maplist(standardize_option(Left, Id), RightOpts, StdRightOpts),
   phrase(compile(rule(Name, [Left-Id], [], [], StdRightOpts) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:analyze(Name, Left, RightOpts), Clauses) :-
   maplist(standardize_option(Left, Id), RightOpts, StdRightOpts),
   phrase(compile(rule(Name, [Left-Id], [], [], StdRightOpts) :- true), Clauses),
   debug_clauses(Clauses).

user:term_expansion((egraph:rewrite(Name, Left, LeftOpts, Right, RightOpts) :- Body), Clauses) :-
   maplist(standardize_option(Right, Id), RightOpts, StdRightOpts),
   maplist(standardize_option(Left, Id), LeftOpts, StdLeftOpts),
   phrase(compile(rule(Name, [Left-Id], StdLeftOpts, [Right-Id], StdRightOpts) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:rewrite(Name, Left, LeftOpts, Right, RightOpts), Clauses) :-
   maplist(standardize_option(Right, Id), RightOpts, StdRightOpts),
   maplist(standardize_option(Left, Id), LeftOpts, StdLeftOpts),
   phrase(compile(rule(Name, [Left-Id], StdLeftOpts, [Right-Id], StdRightOpts) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rewrite(Name, Left, Right, RightOpts) :- Body), Clauses) :-
   maplist(standardize_option(Right, Id), RightOpts, StdRightOpts),
   phrase(compile(rule(Name, [Left-Id], [], [Right-Id], StdRightOpts) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:rewrite(Name, Left, Right, RightOpts), Clauses) :-
   maplist(standardize_option(Right, Id), RightOpts, StdRightOpts),
   phrase(compile(rule(Name, [Left-Id], [], [Right-Id], StdRightOpts) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rewrite(Name, Left, Right) :- Body), Clauses) :-
   phrase(compile(rule(Name, [Left-Id], [], [Right-Id], []) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion(egraph:rewrite(Name, Left, Right), Clauses) :-
   phrase(compile(rule(Name, [Left-Id], [], [Right-Id], []) :- true), Clauses),
   debug_clauses(Clauses).

user:term_expansion((egraph:rule(Name, Lefts, LeftsOpts, Rights, RightsOpts) :- Body), Clauses) :-
   phrase(compile(rule(Name, Lefts, LeftsOpts, Rights, RightsOpts) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rule(Name, Lefts, LeftsOpts, Rights, RightsOpts)), Clauses) :-
   phrase(compile(rule(Name, Lefts, LeftsOpts, Rights, RightsOpts) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rule(Name, Lefts, Rights, RightsOpts) :- Body), Clauses) :-
   phrase(compile(rule(Name, Lefts, [], Rights, RightsOpts) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rule(Name, Lefts, Rights, RightsOpts)), Clauses) :-
   phrase(compile(rule(Name, Lefts, [], Rights, RightsOpts) :- true), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rule(Name, Lefts, Rights) :- Body), Clauses) :-
   phrase(compile(rule(Name, Lefts, [], Rights, []) :- Body), Clauses),
   debug_clauses(Clauses).
user:term_expansion((egraph:rule(Name, Lefts, Rights)), Clauses) :-
   phrase(compile(rule(Name, Lefts, [], Rights, []) :- true), Clauses),
   debug_clauses(Clauses).

:- begin_tests(egraph_compile).

test(explicit_unifs,
     [RightsCopy =@= ['$NODE'(B)-NewId1, c-Id2, d-Id3],
      RightOptsCopy =@= [cost(A, 1), const(Id2, 0), cost(c, 5)],
      Unifs =@= [Id1=NewId1]]) :-
   Lefts = ['$NODE'(A)-Id1],
   Rights = ['$NODE'(B)-Id1, c-Id2, d-Id3],
   RightOpts = [cost(A, 1), const(Id2, 0), cost(c, 5)],
   
   explicit_unifs(Lefts, Rights, RightOpts, RightsCopy, RightOptsCopy, Unifs).
test(explicit_unifs2,
     [RightsCopy =@= [],
      RightOptsCopy =@= [],
      Unifs == [B=AB]]) :-
   Lefts = [_A+B-AB],
   Rights = [B-AB],
   RightOpts = [],
   explicit_unifs(Lefts, Rights, RightOpts, RightsCopy, RightOptsCopy, Unifs),
   print_term(Unifs, []), nl.

test(optimal_order) :-
   Nodes = [
      a(Id2)-node(Id4, 1),
      b(Id1, Id2)-node(Id3, 1),
      c-node(Id1, 1)
   ],
   OutputVars = [Id3, Id4],
   
   optimal_order(Nodes, OutputVars, Plan),
   
   % The optimal order should start with the most constrained node 'c',
   % then follow the shared variables to 'b', and finally 'a'.
   Plan == [
      c-node(Id1, 1),
      b(Id1, Id2)-node(Id3, 1),
      a(Id2)-node(Id4, 1)
   ].

test(optimal_order_matchall, [Plan == [a-node(Id1, 1), PatVar-node(Id1, 1)]]) :-
   % Instantiated patterns are prioritized over matchall variables 
   % thanks to the PatCost addition in the heuristic.
   Nodes = [
      PatVar-node(Id1, 1),
      a-node(Id1, 1)
   ],
   OutputVars = [],
   
   optimal_order(Nodes, OutputVars, Plan).

test(compile) :-
   Rule = (rule(my_rule, [f(A, B)-Id1, a-A, b-B], [], [g(B, A)-Id1], []) :- true),
   phrase(compile(Rule), Clauses),
   is_list(Clauses),
   Clauses \== [].

:- end_tests(egraph_compile).
