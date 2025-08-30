:- use_module(egraph3).
:- use_module(library(plunit)).
:- use_module(library(rbtrees)).

% lookup/2
:- begin_tests(lookup).

% Finds the Id in a 1-element canonical list
test(lookup_found_singleton, true(V == X)) :-
    X = _,
    egraph:lookup(a-V, [a-X]).

% Finds the Id in a multi-element canonical list
test(lookup_found_multi, true(V == Y)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(b-V, [a-X, b-Y, c-Z]).

% Fails on empty list
test(lookup_fail_empty, fail) :-
    egraph:lookup(a-_, []).

% Fails when Key is absent from a canonical list
test(lookup_fail_absent, fail) :-
    X = _, Y = _, Z = _,
    egraph:lookup(d-_, [a-X, b-Y, c-Z]).

:- end_tests(lookup).


% add//2 and add/4
:- begin_tests(add).

% Add atom: second add reuses the same Id
test(add_atom_reuse_id, true(Id2==Id)) :-
    egraph:add(a, Id, [], Out1),
    egraph:add(a, Id2, Out1, _Out2).

% Add atom: set is unchanged on reuse
test(add_atom_no_set_change, true(Out2==Out1)) :-
    egraph:add(a, Id, [], Out1),
    egraph:add(a, _Id2, Out1, Out2).

% Add compound: left child added as node a-A
test(add_compound_child_left, true(member(a-A, Out))) :-
    egraph:add(f(a,b), _Id, [], Out).

% Add compound: right child added as node b-B
test(add_compound_child_right, true(member(b-B, Out))) :-
    egraph:add(f(a,b), _Id, [], Out).

% Add compound: parent node uses child Ids f(A,B)-Id
test(add_compound_parent_uses_child_ids, true(member(f(A,B)-Id, Out))) :-
    egraph:add(f(a,b), Id, [], Out).

% DCG form: add//2 builds nodes via phrase/3
test(add_dcg_atom, true(Out == [a-Id])) :-
    phrase(egraph:add(a, Id), [], Out).

:- end_tests(add).


% add_node/3 and add_node/4
:- begin_tests(add_node).

% Inserting a new node produces it with a fresh Id
test(add_node_insert_member, true(member(x-Id, Out))) :-
    egraph:add_node(x, Id, [], Out).

% Inserting a new node yields a singleton set
test(add_node_insert_len1, true(length(Out,1))) :-
    egraph:add_node(x, _Id, [], Out).

% Re-adding an existing node reuses Id
test(add_node_reuse_id, true(Id==X)) :-
    X = _,
    In = [x-X],
    egraph:add_node(x, Id, In, _Out).

% Re-adding an existing node does not change the set
test(add_node_reuse_noop, true(Out==In)) :-
    X = _,
    In = [x-X],
    egraph:add_node(x, _Id, In, Out).

% Pair form delegates and uses provided Id
test(add_node_pair_form_member, true(member(y-Y, Out))) :-
    X = _,
    egraph:add_node(y-Y, [x-X], Out).

:- end_tests(add_node).


% union//2 and union/4
:- begin_tests(union).

% Unifies the two Ids (aliases classes)
test(union_alias_ids, true(A==B)) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [x-A, y-B], _Out).

% Preserves both distinct keys after alias
test(union_keeps_both_keys, true((member(x-A, Out), member(y-A, Out)))) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [x-A, y-B], Out).

% Union inside a pipeline aliases A with f(f(a))
test(union_dcg_pipeline_alias, true(A==FFA)) :-
    phrase((egraph:add(a, A),
            egraph:add(f(f(a)), FFA),
            egraph:union(A, FFA)), [], _Out).

% Union on same Id is a no-op on the set
test(union_same_id_noop, true(Out == [x-A])) :-
    A = _,
    phrase(egraph:union(A, A), [x-A], Out).

:- end_tests(union).


% merge_nodes//0 and merge_nodes/2
:- begin_tests(merge_nodes).

% DCG form is a no-op on empty set
test(merge_nodes_dcg_empty_noop, true(Out == [])) :-
    phrase(egraph:merge_nodes, [], Out).

% Duplicate keys are deduplicated to a single representative pair
test(merge_nodes_dedup_output_single_key, true(Out == [x-A])) :-
    A = _, B = _,
    egraph:merge_nodes([x-A, x-B], Out).

% Dedup unifies Ids in the duplicate group
test(merge_nodes_dedup_alias_ids, true(A==B)) :-
    A = _, B = _,
    egraph:merge_nodes([x-A, x-B], _Out).

% Idempotent on canonical input
test(merge_nodes_idempotent, true(Out == In)) :-
    A = _, B = _,
    In = [a-A, b-B],
    egraph:merge_nodes(In, Out).

% Id aliasing can instantiate variables inside Keys and collapses collisions
test(merge_nodes_alias_instantiates_keys_member, true(member(f(A)-FA, Out))) :-
    A = _, B = _, FA = _, FB = _,
    In = [a-A, b-B, f(A)-FA, f(B)-FB],
    A = B,
    egraph:merge_nodes(In, Out).

% Id aliasing makes function-key Ids equal
test(merge_nodes_alias_instantiates_keys_ids_equal, true(FB==FA)) :-
    A = _, B = _, FA = _, FB = _,
    In = [a-A, b-B, f(A)-FA, f(B)-FB],
    A = B,
    egraph:merge_nodes(In, Out),
    _ = Out.

:- end_tests(merge_nodes).


% merge_group/4
:- begin_tests(merge_group).

% Non-trivial group: tail Id B is unified with head A
test(merge_group_tail_unified_with_head, true(B==A)) :-
    A = _, B = _,
    egraph:merge_group(x-[A,B], _RepPair, false, _Changed).

% Non-trivial group: representative is the head Id
test(merge_group_rep_is_head, true(Rep==A)) :-
    A = _, B = _,
    egraph:merge_group(x-[A,B], x-Rep, false, _Changed).

% Non-trivial group: Changed is set to true when merging occurs
test(merge_group_sets_changed_true, true(Changed)) :-
    A = _, B = _,
    egraph:merge_group(x-[A,B], _RepPair, false, Changed).

% Single-element group: representative is the sole Id
test(merge_group_single_repunchanged, true(Rep==A)) :-
    A = _,
    egraph:merge_group(x-[A], x-Rep, false, _).

% Single-element group: Changed flag preserved
test(merge_group_single_changed_preserved, true(Changed0==Changed)) :-
    A = _, Changed0 = false,
    egraph:merge_group(x-[A], _RepPair, Changed0, Changed).

:- end_tests(merge_group).


% comm//2
:- begin_tests(comm).

% Emits commuted variant b+a-BA from (A+B)-AB
test(comm_emits_commuted_node, true(member(b+a-BA, Out))) :-
    A = _, B = _, AB = _,
    phrase(egraph:comm((A+B)-AB, _Index), [], Out).

% Emits equality AB=BA
test(comm_emits_equality, true(member(AB=BA, Out))) :-
    A = _, B = _, AB = _,
    phrase(egraph:comm((A+B)-AB, _Index), [], Out).

% The emitted Ids BA and AB are variables
test(comm_ids_are_vars, true((var(BA), var(AB)))) :-
    A = _, B = _, AB = _,
    phrase(egraph:comm((A+B)-AB, _Index), [], [ _ - BA_Node, AB=BA ]),
    BA_Node = BA.

% Non-match produces no output
test(comm_nomatch_empty, true(Out == [])) :-
    Id = _,
    phrase(egraph:comm(foo-Id, _Idx), [], Out).

:- end_tests(comm).


% assoc//2
:- begin_tests(assoc).

% Emits A+B-AB when class(BC) includes +(B,C)
test(assoc_emits_ab, true(member(A+B-AB, Out))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), [], Out).

% Emits AB+C-ABC_
test(assoc_emits_abc_, true(member(AB+C-ABC_, Out))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), [], Out).

% Emits equality ABC=ABC_
test(assoc_emits_eq, true(member(ABC=ABC_, Out))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), [], Out).

% No mapping for BC in Index => no output
test(assoc_nomap_empty, true(Out == [])) :-
    A = _, BC = _, ABC = _,
    ord_list_to_rbtree([], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), [], Out).

:- end_tests(assoc).


% assoc_//3
:- begin_tests(assoc_).

% Skips non-+(B,C) members; emits only for matching b+c
test(assoc__filters_emission_ab, true(member(a+b-AB, Out))) :-
    AB = _, ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), [], Out).

% Emits AB+C-ABC_ for matching b+c
test(assoc__filters_emission_abc_, true(member(AB+c-ABC_, Out))) :-
    AB = _, ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), [], Out).

% Emits equality ABC=ABC_
test(assoc__filters_emission_eq, true(member(ABC=ABC_, Out))) :-
    AB = _, ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), [], Out).

:- end_tests(assoc_).


% reduce//2
:- begin_tests(reduce).

% If class(B) contains 0, reduce A+B to A=AB
test(reduce_has_zero_emits_eq, true(Out == [A=AB])) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[0, 1]], Index),
    phrase(egraph:reduce(A+B-AB, Index), [], Out).

% If class(B) lacks 0, no reduction
test(reduce_no_zero_no_output, true(Out == [])) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[1, 2]], Index),
    phrase(egraph:reduce(A+B-AB, Index), [], Out).

:- end_tests(reduce).


% constant_folding//2
:- begin_tests(constant_folding).

% Folds numeric sums; skips non-numeric class members in A
test(const_fold_numeric_only_pair, true(member(5-C1, Out))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([A-[2, foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-AB, Index), [], Out).

% Folds numeric sums; emits equality C=AB
test(const_fold_numeric_only_eq, true(member(C1=AB, Out))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([A-[2, foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-AB, Index), [], Out).

% Skips when class(A) has no numeric members
test(const_fold_skips_non_numeric_A, true(Out == [])) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([A-[foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-AB, Index), [], Out).

:- end_tests(constant_folding).


% constant_folding_a//4
:- begin_tests(constant_folding_a).

% Emits 5-C for VA=2 and VB=3
test(const_fold_a_emits_5_pair, true(member(5-C, Out))) :-
    B = _, AB = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, AB, Index), [], Out).

% Emits 9-C2 for VA=2 and VB=7
test(const_fold_a_emits_9_pair, true(member(9-C2, Out))) :-
    B = _, AB = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, AB, Index), [], Out).

% Emits equalities C=AB and C2=AB
test(const_fold_a_emits_equalities, true((member(C=AB, Out), member(C2=AB, Out)))) :-
    B = _, AB = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, AB, Index), [], Out).

:- end_tests(constant_folding_a).


% constant_folding_b//4
:- begin_tests(constant_folding_b).

% Filters VB by number/1 and emits value pair
test(const_fold_b_filters_pair, true(member(5-C, Out))) :-
    AB = _,
    phrase(egraph:constant_folding_b([3, foo], 2, AB, _Index), [], Out).

% Emits equality C=AB for numeric VB
test(const_fold_b_filters_eq, true(member(C=AB, Out))) :-
    AB = _,
    phrase(egraph:constant_folding_b([3, foo], 2, AB, _Index), [], Out).

:- end_tests(constant_folding_b).


% rules//3
:- begin_tests(rules).

% Applies comm then reduce; contains commuted node b+a-BA
test(rules_apply_order_commuted_node, true(member(b+a-BA, Out))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), [], Out).

% Applies comm then reduce; contains equality AB=BA
test(rules_apply_order_comm_eq, true(member(AB=BA, Out))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), [], Out).

% Applies comm then reduce; contains reduction A=AB
test(rules_apply_order_reduce_eq, true(member(A=AB, Out))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), [], Out).

:- end_tests(rules).


% rule//3
:- begin_tests(rule).

% Wrapper invokes comm rule: emits commuted node
test(rule_wrapper_comm_node, true(member(b+a-BA, Out))) :-
    A = _, B = _, AB = _,
    phrase(egraph:rule(_Index, (A+B)-AB, comm), [], Out).

% Wrapper invokes comm rule: emits equality
test(rule_wrapper_comm_eq, true(member(AB=BA, Out))) :-
    A = _, B = _, AB = _,
    phrase(egraph:rule(_Index, (A+B)-AB, comm), [], Out).

:- end_tests(rule).


% make_index/2
:- begin_tests(make_index).

% Builds rbtree: class(A) has keys [x,y]
test(make_index_class_a_keys, true(SortedA == [x,y])) :-
    A = _, B = _,
    Nodes = [x-A, y-A, z-B],
    egraph:make_index(Nodes, Index),
    rb_lookup(A, KeysA, Index),
    sort(KeysA, SortedA).

% Builds rbtree: class(B) has key [z]
test(make_index_class_b_key, true(KeysB == [z])) :-
    A = _, B = _,
    Nodes = [x-A, y-A, z-B],
    egraph:make_index(Nodes, Index),
    rb_lookup(B, KeysB, Index).

:- end_tests(make_index).


% match/4
:- begin_tests(match).

% Runs comm over worklist: contains commuted node
test(match_comm_node, true(member(b+a-BA, Matches))) :-
    A = _, B = _, AB = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([], Index),
    egraph:match([comm], Work, Index, Matches).

% Runs comm over worklist: contains equality
test(match_comm_eq, true(member(AB=BA, Matches))) :-
    A = _, B = _, AB = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([], Index),
    egraph:match([comm], Work, Index, Matches).

:- end_tests(match).


% push_back//1
:- begin_tests(push_back).

% Appends its list to DCG output
test(push_back_appends, true(Out == [a,b])) :-
    phrase(egraph:push_back([a,b]), [], Out).

:- end_tests(push_back).


% rebuild//1
:- begin_tests(rebuild).

% Aliases Ids for (=)/2 matches
test(rebuild_aliases_ids, true(A==B)) :-
    A = _, B = _, C = _,
    In = [x-A, y-B],
    Matches = [A=B, z-C],
    phrase(egraph:rebuild(Matches), In, _Out).

% Enqueues new nodes from Matches
test(rebuild_enqueues_nodes, true(member(z-C, Out))) :-
    A = _, B = _, C = _,
    In = [x-A, y-B],
    Matches = [A=B, z-C],
    phrase(egraph:rebuild(Matches), In, Out).

% Canonicalizes after alias: both keys map to aliased Id
test(rebuild_canonicalizes_x, true(member(x-A, Out))) :-
    A = _, B = _, C = _,
    In = [x-A, y-B],
    Matches = [A=B, z-C],
    phrase(egraph:rebuild(Matches), In, Out).

% Canonicalizes after alias: y key maps to aliased Id
test(rebuild_canonicalizes_y, true(member(y-A, Out))) :-
    A = _, B = _, C = _,
    In = [x-A, y-B],
    Matches = [A=B, z-C],
    phrase(egraph:rebuild(Matches), In, Out).

:- end_tests(rebuild).


% saturate//1, saturate//2, saturate/4
:- begin_tests(saturate).

% saturate//1 adds exactly one new node for comm and reaches fixpoint
test(saturate_fixpoint_adds_one, true(L2 is L1 + 1)) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    length(G0, L1),
    phrase(egraph:saturate([comm]), G0, G2),
    length(G2, L2).

% saturate//1 result contains the commuted node
test(saturate_fixpoint_contains_commuted, true(member(2+1-AB, G2))) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    phrase(egraph:saturate([comm]), G0, G2).

% saturate//1 result contains the original node
test(saturate_fixpoint_contains_original, true(member(1+2-AB, G2))) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    phrase(egraph:saturate([comm]), G0, G2).

% saturate//2 with MaxSteps=0 leaves graph unchanged
test(saturate_zero_steps_no_change, true(G == G0)) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    phrase(egraph:saturate([comm], 0), G0, G).

% saturate/4 one step grows by exactly one node for comm rule
test(saturate_driver_one_step_grows_by_one, true(L0p1 is L0 + 1)) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    egraph:saturate([comm], 1, G0, G1),
    length(G0, L0),
    length(G1, L0p1).

:- end_tests(saturate).


% unif/1
:- begin_tests(unif).

% Unifies arguments when given an equality term
test(unif_does_unify, true(A==B)) :-
    A = _, B = _,
    egraph:unif(A=B).

% Fails for non-equality term
test(unif_fails_non_equality, fail) :-
    egraph:unif(foo).

:- end_tests(unif).


% extract/1
:- begin_tests(extract).

% Aliases Ids to a representative Key (one per class)
test(extract_aliases_ids_to_member, true((A==x ; A==y))) :-
    A = _,
    Nodes = [x-A, y-A],
    egraph:extract(Nodes).

:- end_tests(extract).


% extract//0
:- begin_tests(extract_dcg).

% DCG wrapper succeeds and aliases through Nodes
test(extract_dcg_aliases, true((A==x ; A==y))) :-
    A = _,
    Nodes = [x-A, y-A],
    phrase(egraph:extract, Nodes, Nodes).

:- end_tests(extract_dcg).


% extract/2
:- begin_tests(extract_2).

% Semidet form: succeeds and aliases within Nodes
test(extract_2_semidet_aliases, true((A==x ; A==y))) :-
    A = _,
    Nodes = [x-A, y-A],
    egraph:extract(Nodes, Nodes).

:- end_tests(extract_2).


% extract_node/1
:- begin_tests(extract_node).

% Chooses a member per Id group (once/1 to commit)
test(extract_node_chooses_members, true((A==x, B==z))) :-
    A = _, B = _,
    Groups = [A-[x,y], B-[z]],
    once(egraph:extract_node(Groups)).

:- end_tests(extract_node).


% add_expr/2
:- begin_tests(add_expr).

% Builds right-associated sum 1+2+...+N
test(add_expr_right_assoc, true(Expr == 1+(2+3))) :-
    egraph:add_expr(3, Expr).

% N=1 yields 1
test(add_expr_n1_is_1, true(Expr == 1)) :-
    egraph:add_expr(1, Expr).

:- end_tests(add_expr).


% example1/1
:- begin_tests(example1).

% Graph contains a-A
test(example1_contains_a, true(member(a-A, G))) :-
    egraph:example1(G).

% Graph contains f^4(a)
test(example1_contains_f4a, true(member(f(f(f(f(a))))-Id, G))) :-
    egraph:example1(G).

% Ids for a and f^4(a) are aliased
test(example1_ids_aliased, true(A==Id)) :-
    member(a-A, G),
    member(f(f(f(f(a))))-Id, G),
    egraph:example1(G).

:- end_tests(example1).


% example2/2
:- begin_tests(example2).

% Returns the built Expr; side effects are timing/printing which we ignore
test(example2_returns_expr, true(Expr == 1+(2+3))) :-
    with_output_to(string(_), egraph:example2(3, Expr)).

:- end_tests(example2).


% example3/3
:- begin_tests(example3).

% For N=1 and Expr=1, the only extracted result is 1
test(example3_n1_only_1, true(Rs == [1])) :-
    findall(R, egraph:example3(1, 1, R), Rs).

% For N=2 and Expr=1+2, one possible extracted result is 3
test(example3_n2_includes_3, true(member(3, Rs))) :-
    egraph:add_expr(2, Expr),
    findall(R, egraph:example3(2, Expr, R), Rs).

:- end_tests(example3).
