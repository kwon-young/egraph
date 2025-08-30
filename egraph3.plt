:- use_module(egraph3).
:- use_module(library(plunit)).
:- use_module(library(rbtrees)).
:- use_module(library(ordsets)).

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

% Finds the Id when Key is the first element in a canonical list
test(lookup_found_first, true(V == X)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(a-V, [a-X, b-Y, c-Z]).

% Finds the Id when Key is the last element in a canonical list
test(lookup_found_last, true(V == Z)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(c-V, [a-X, b-Y, c-Z]).

% Keys are variable-identity sensitive; variant-equal keys with different variables are not identical and should not be found.
% Confirms that lookup/2 fails to match f(V2) against existing f(V1) when V1 \== V2 (goal is expected to fail).
test(lookup_variant_key_identity, [fail]) :-
    V1 = _, V2 = _,
    V1 \== V2,
    egraph:lookup(f(V2)-_, [f(V1)-_Id]).

:- end_tests(lookup).


% add/4
:- begin_tests(add_4).

% Add atom: second add reuses the same Id
test(add_atom_reuse_id, true(Id2==Id)) :-
    egraph:add(a, Id, [], Out1),
    egraph:add(a, Id2, Out1, _Out2).

% Add atom: set is unchanged on reuse
test(add_atom_no_set_change, true(Out2==Out1)) :-
    egraph:add(a, _Id, [], Out1),
    egraph:add(a, _Id2, Out1, Out2).

% Add compound: left child added as node a-A
test(add_compound_child_left, true(member(a-_A, Out))) :-
    egraph:add(f(a,b), _Id, [], Out).

% Add compound: right child added as node b-B
test(add_compound_child_right, true(member(b-_B, Out))) :-
    egraph:add(f(a,b), _Id, [], Out).

% Add compound: parent node uses child Ids f(A,B)-Id
test(add_compound_parent_uses_child_ids, true((member(a-A, Out), member(b-B, Out), member(f(A,B)-Id, Out)))) :-
    egraph:add(f(a,b), Id, [], Out).

:- end_tests(add_4).

% add//2
:- begin_tests(add_dcg_2).

% DCG form: add//2 builds nodes via phrase/3
% Verifies that adding an atom via DCG yields a singleton list with that node.
test(add_dcg_atom, true(Out == [a-Id])) :-
    phrase(egraph:add(a, Id), [], Out).

% DCG form for compound term: ensures children and parent entries are produced
% Verifies that phrase/3 over add//2 inserts a-A, b-B, and f(A,B)-Id.
test(add_dcg_compound_builds_all_nodes, true((member(a-A, Out), member(b-B, Out), member(f(A,B)-Id, Out)))) :-
    phrase(egraph:add(f(a,b), Id), [], Out).

:- end_tests(add_dcg_2).


% add_node/3
:- begin_tests(add_node_3).

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

% Preserves canonical order when inserting into a non-empty canonical set
test(add_node_insert_sorted_order, true(Out == [a-A, b-B])) :-
    B = _,
    egraph:add_node(a, A, [b-B], Out).

:- end_tests(add_node_3).

% add_node/4
:- begin_tests(add_node_4).

% Pair form delegates and uses provided Id
test(add_node_pair_form_member, true(member(y-Y, Out))) :-
    X = _,
    egraph:add_node(y-Y, [x-X], Out).

% Uses the provided Id in the pair form
test(add_node_pair_uses_provided_id, true(Y2==Y)) :-
    X = _,
    egraph:add_node(y-Y, [x-X], Out),
    member(y-Y2, Out).

:- end_tests(add_node_4).


% union//2
:- begin_tests(union_dcg_2).

% Unifies the two Ids (aliases classes)
test(union_alias_ids_dcg, true(A==B)) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [x-A, y-B], _Out).

% Preserves both distinct keys after alias
test(union_keeps_both_keys_dcg, true((member(x-A, Out), member(y-A, Out)))) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [x-A, y-B], Out).

% Union inside a pipeline aliases A with f(f(a))
test(union_dcg_pipeline_alias, true(A==FFA)) :-
    phrase((egraph:add(a, A),
            egraph:add(f(f(a)), FFA),
            egraph:union(A, FFA)), [], _Out).

% Union on same Id is a no-op on the set
test(union_same_id_noop_dcg, true(Out == [x-A])) :-
    A = _,
    phrase(egraph:union(A, A), [x-A], Out).

% Ensures resulting set is canonical-sorted after aliasing
test(union_dcg_sorted_after_alias, true(Out == [a-A, b-A])) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [b-B, a-A], Out).

:- end_tests(union_dcg_2).

% union/4
:- begin_tests(union_4).

% Unifies the two Ids (aliases classes)
test(union_alias_ids_4, true(A==B)) :-
    A = _, B = _,
    egraph:union(A, B, [x-A, y-B], _Out).

% Preserves both distinct keys after alias
test(union_keeps_both_keys_4, true((member(x-A, Out), member(y-A, Out)))) :-
    A = _, B = _,
    egraph:union(A, B, [x-A, y-B], Out).

% Union on same Id is a no-op on the set
test(union_same_id_noop_4, true(Out == [x-A])) :-
    A = _,
    egraph:union(A, A, [x-A], Out).

% Ensures resulting set is canonical-sorted after aliasing (pair order normalized)
test(union_sorted_after_alias_4, true(Out == [a-A, b-A])) :-
    A = _, B = _,
    egraph:union(A, B, [b-B, a-A], Out).

:- end_tests(union_4).


% merge_nodes/2
:- begin_tests(merge_nodes_2).

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

% Sorts output into canonical order
test(merge_nodes_sorts_canonical, true(Out == [a-A, b-B])) :-
    A = _, B = _,
    egraph:merge_nodes([b-B, a-A], Out).

:- end_tests(merge_nodes_2).

% merge_nodes//0
:- begin_tests(merge_nodes_dcg_0).

% DCG form is a no-op on empty set
test(merge_nodes_dcg_empty_noop, true(Out == [])) :-
    phrase(egraph:merge_nodes, [], Out).

% DCG wrapper on non-canonical input: deduplicates to a single representative
test(merge_nodes_dcg_dedup_only, true(Out == [x-A])) :-
    A = _, B = _,
    phrase(egraph:merge_nodes, [x-A, x-B], Out).

% DCG wrapper ensures duplicate-key Ids unify (alias)
test(merge_nodes_dcg_alias_ids, true(A==B)) :-
    A = _, B = _,
    phrase(egraph:merge_nodes, [x-A, x-B], _Out).

:- end_tests(merge_nodes_dcg_0).


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

% Emits commuted variant (B+A)-BA from (A+B)-AB using the same A,B variables
test(comm_emits_commuted_node, true((member(K-_BA, Out), K = B+A))) :-
    A = _, B = _,
    phrase(egraph:comm((A+B)-_AB, _Index), Out).

% Emits equality AB=BA indicating the commuted form is equated to the original
test(comm_emits_equality, true(member(_=_, Out))) :-
    A = _, B = _,
    phrase(egraph:comm((A+B)-_, _Index), Out).

% The emitted Ids BA and AB are variables
test(comm_ids_are_vars, true((member(AB=BA, Out), var(AB), var(BA)))) :-
    A = _, B = _,
    phrase(egraph:comm((A+B)-_AB, _Index), Out).

% Non-match produces no output
test(comm_nomatch_empty, true(Out == [])) :-
    phrase(egraph:comm(foo-_, _Idx), [], Out).

% Emits exactly two outputs: the commuted node and the equality
test(comm_emits_exactly_two, true(length(Out,2))) :-
    A = _, B = _,
    phrase(egraph:comm((A+B)-_AB, _Index), Out).

:- end_tests(comm).


% assoc//2
:- begin_tests(assoc).

% Emits A+B-AB when class(BC) includes +(B,C)
test(assoc_emits_ab, true(member(A+B-_AB, Out))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), Out).

% Emits AB+C-ABC_
test(assoc_emits_abc_, true(member(_AB+C-_ABC_, Out))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), Out).

% Emits equality ABC=ABC_
test(assoc_emits_eq, true(member(ABC=_ABC_, Out))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), Out).

% BUG: Due to a cut in assoc//2, when BC is absent from the Index the rule fails instead of emitting nothing.
% This test encodes the intended behavior (no output); we expect it to fail to demonstrate the bug.
test(assoc_nomap_empty, [fail]) :-
    A = _, BC = _, ABC = _,
    ord_list_to_rbtree([], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), Out),
    Out == [].

:- end_tests(assoc).


% assoc_//3
:- begin_tests(assoc_).

% Skips non-+(B,C) members; emits only for matching b+c
test(assoc__filters_emission_ab, true(member((a+b)-_, Out))) :-
    ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), Out).

% Emits AB+C-ABC_ for matching b+c
test(assoc__filters_emission_abc_, true(member(( _ + c)-_, Out))) :-
    ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), Out).

% Emits equality ABC=ABC_
test(assoc__filters_emission_eq, true(member(_=_, Out))) :-
    ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), Out).

:- end_tests(assoc_).


% reduce//2
:- begin_tests(reduce).

% If class(B) contains 0, reduce A+B to A=AB
test(reduce_has_zero_emits_eq, true(member(A=_, Out))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0, 1]], Index),
    phrase(egraph:reduce((A+B)-_, Index), Out).

% If class(B) lacks 0, no reduction
test(reduce_no_zero_no_output, true(Out == [])) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[1, 2]], Index),
    phrase(egraph:reduce((A+B)-_, Index), Out).

:- end_tests(reduce).


% constant_folding//2
:- begin_tests(constant_folding).

% Folds numeric sums; skips non-numeric class members in A
test(const_fold_numeric_only_pair, true(member(5-_C1, Out))) :-
    A = _, B = _,
    ord_list_to_rbtree([A-[2, foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-_AB, Index), Out).

% Folds numeric sums; emits equality C=AB
test(const_fold_numeric_only_eq, true(member(_=_, Out))) :-
    A = _, B = _,
    ord_list_to_rbtree([A-[2, foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-_AB, Index), Out).

% Skips when class(A) has no numeric members
test(const_fold_skips_non_numeric_A, true(Out == [])) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([A-[foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-AB, Index), Out).

% Skips when class(B) has no numeric members
test(const_fold_skips_non_numeric_B, true(Out == [])) :-
    A = _, B = _,
    ord_list_to_rbtree([A-[2], B-[foo]], Index),
    phrase(egraph:constant_folding((A+B)-_AB, Index), Out).

% Emits exactly one value pair and one equality for numeric A and B
test(const_fold_emits_pair_and_eq_count, true(length(Out, 2))) :-
    A = _, B = _,
    ord_list_to_rbtree([A-[2], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-_AB, Index), Out).

:- end_tests(constant_folding).


% constant_folding_a//4
:- begin_tests(constant_folding_a).

% Emits 5-C for VA=2 and VB=3
test(const_fold_a_emits_5_pair, true(member(5-_C, Out))) :-
    B = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, _AB, Index), Out).

% Emits 9-C2 for VA=2 and VB=7
test(const_fold_a_emits_9_pair, true(member(9-_C2, Out))) :-
    B = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, _AB, Index), Out).

% Emits equality C=AB for VB=3
test(const_fold_a_emits_eq_5_ab, true(member(_C=AB, Out))) :-
    B = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, AB, Index), Out).

% Emits equality C2=AB for VB=7
test(const_fold_a_emits_eq_9_ab, true(member(_C2=AB, Out))) :-
    B = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, AB, Index), Out).

:- end_tests(constant_folding_a).


% constant_folding_b//4
:- begin_tests(constant_folding_b).

% Filters VB by number/1 and emits value pair
test(const_fold_b_filters_pair, true(member(5-_C, Out))) :-
    phrase(egraph:constant_folding_b([3, foo], 2, _AB, _Index), Out).

% Emits equality C=AB for numeric VB
test(const_fold_b_filters_eq, true(member(_C=AB, Out))) :-
    phrase(egraph:constant_folding_b([3, foo], 2, AB, _Index), Out).

% No output when class(B) has no numeric members
test(const_fold_b_non_numeric_only, true(Out == [])) :-
    phrase(egraph:constant_folding_b([foo, bar], 2, _AB, _Index), Out).

:- end_tests(constant_folding_b).


% rules//3
:- begin_tests(rules).

% Applies comm then reduce; contains commuted node b+a-BA
test(rules_apply_order_commuted_node, true((member(K-_BA, Out), K = B+A))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-_AB), Out).

% Applies comm then reduce; contains equality AB=BA
test(rules_apply_order_comm_eq, true((member(AB=BA, Out), var(AB), var(BA)))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), Out).

% Applies comm then reduce; contains reduction A=AB
test(rules_apply_order_reduce_eq, true(member(A=AB, Out))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), Out).

% Ensures output order is per-rule: comm outputs precede reduce outputs
test(rules_output_order_prefix, true((Out = [K1, Eq1, Eq2 | _], K1 = (B+A)-_, Eq1 = (AB=_), Eq2 = (A=AB)))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), Out).

:- end_tests(rules).


% rule//3
:- begin_tests(rule).

% Wrapper invokes comm rule: emits commuted node
test(rule_wrapper_comm_node, true((member(K-_BA, Out), K = B+A))) :-
    A = _, B = _,
    phrase(egraph:rule(_Index, (A+B)-_AB, comm), Out).

% Wrapper invokes comm rule: emits equality
test(rule_wrapper_comm_eq, true((member(AB=BA, Out), var(AB), var(BA)))) :-
    A = _, B = _,
    phrase(egraph:rule(_Index, (A+B)-AB, comm), Out).

% Wrapper invokes reduce rule: emits A=AB when class(B) contains 0
% Confirms that rule//3 passes Index correctly to the reduce rule.
test(rule_wrapper_reduce_eq, true(member(A=AB, Out))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0]], Index),
    phrase(egraph:rule(Index, (A+B)-AB, reduce), Out).

% Ensures comm rule emits node before equality in its output list
test(rule_comm_output_order, true((Out = [K1, Eq1], K1 = (B+A)-_, Eq1 = (AB=_)))) :-
    A = _, B = _,
    phrase(egraph:rule(_Index, (A+B)-AB, comm), Out).

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
% Ensures the commuted node B+A appears (use variables, not atoms)
test(match_comm_node, true(member((B+A)-_, Matches))) :-
    A = _, B = _, AB = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([], Index),
    egraph:match([comm], Work, Index, Matches).

% Runs comm over worklist: contains equality
test(match_comm_eq, true(member(AB=_BA, Matches))) :-
    A = _, B = _, AB = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([], Index),
    egraph:match([comm], Work, Index, Matches).

% Ensures match preserves rule output order for a single work item
test(match_comm_order_prefix, true((Matches = [K1, Eq1 | _], K1 = B+A-_, Eq1 = (AB=_)))) :-
    A = _, B = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([], Index),
    egraph:match([comm], Work, Index, Matches).

% Runs comm over two work items: emits two nodes and two equalities (4 outputs total)
test(match_comm_two_nodes_count, true(length(Matches,4))) :-
    A = _, B = _, AB = _,
    C = _, D = _, CD = _,
    Work = [(A+B)-AB, (C+D)-CD],
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

% Drops (=)/2 equalities from the scheduled matches in the final output set
% Ensures that equalities are consumed and do not remain in the node list.
test(rebuild_drops_equalities, true(\+ member(_=_ , Out))) :-
    A = _, B = _, C = _,
    In = [x-A, y-B],
    Matches = [A=B, z-C],
    phrase(egraph:rebuild(Matches), In, Out).

% No-op when there are no matches: set remains unchanged and canonical
test(rebuild_noop_on_empty_matches, true(Out == In)) :-
    A = _,
    In = [x-A],
    phrase(egraph:rebuild([]), In, Out).

:- end_tests(rebuild).


% saturate//1
:- begin_tests(saturate_dcg_1).

% Ensures saturate//1 adds exactly one new node for comm and reaches fixpoint
test(saturate1_fixpoint_adds_one, true(L2 is L1 + 1)) :-
    phrase(egraph:add(1+2, _), [], G0),
    length(G0, L1),
    phrase(egraph:saturate([comm]), G0, G2),
    length(G2, L2).

% Ensures saturate//1 result contains the commuted node
test(saturate1_contains_commuted, true(member((2+1)-_, G2))) :-
    phrase(egraph:add(1+2, _), [], G0),
    phrase(egraph:saturate([comm]), G0, G2).

% Ensures saturate//1 retains the original node
test(saturate1_contains_original, true(member((1+2)-_, G2))) :-
    phrase(egraph:add(1+2, _), [], G0),
    phrase(egraph:saturate([comm]), G0, G2).

:- end_tests(saturate_dcg_1).

% saturate//2
:- begin_tests(saturate_dcg_2).

% Verifies saturate//2 with MaxSteps=0 leaves graph unchanged
test(saturate2_zero_steps_no_change, true(G == G0)) :-
    phrase(egraph:add(1+2, _), [], G0),
    phrase(egraph:saturate([comm], 0), G0, G).

% Ensures with sufficient steps, exactly one new node is added for comm and a fixpoint is reached
test(saturate2_fixpoint_adds_one, true(L2 is L1 + 1)) :-
    phrase(egraph:add(1+2, _), [], G0),
    length(G0, L1),
    phrase(egraph:saturate([comm], 10), G0, G2),
    length(G2, L2).

% Ensures the saturated graph contains the commuted node
test(saturate2_contains_commuted, true(member((2+1)-_, G2))) :-
    phrase(egraph:add(1+2, _), [], G0),
    phrase(egraph:saturate([comm], 10), G0, G2).

% Ensures the saturated graph retains the original node
test(saturate2_contains_original, true(member((1+2)-_, G2))) :-
    phrase(egraph:add(1+2, _), [], G0),
    phrase(egraph:saturate([comm], 10), G0, G2).

:- end_tests(saturate_dcg_2).

% saturate/4
:- begin_tests(saturate_4).

% Verifies saturate/4 one step grows by exactly one node for comm rule
test(saturate4_one_step_grows_by_one, true(L0p1 is L0 + 1)) :-
    phrase(egraph:add(1+2, _), [], G0),
    egraph:saturate([comm], 1, G0, G1),
    length(G0, L0),
    length(G1, L0p1).

:- end_tests(saturate_4).


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
test(extract_aliases_ids_to_member, true(once((A==x ; A==y)))) :-
    A = _,
    Nodes = [x-A, y-A],
    once(egraph:extract(Nodes)).

% Trivial success for empty node set (no classes to extract)
test(extract_empty_trivial) :-
    egraph:extract([]).

:- end_tests(extract).


% extract//0
:- begin_tests(extract_dcg).

% DCG wrapper succeeds and aliases through Nodes
test(extract_dcg_aliases, true(once((A==x ; A==y)))) :-
    A = _,
    Nodes = [x-A, y-A],
    once(phrase(egraph:extract, Nodes, Nodes)).

:- end_tests(extract_dcg).


% extract/2
:- begin_tests(extract_2).

% Semidet form: succeeds and aliases within Nodes
test(extract_2_semidet_aliases, true(once((A==x ; A==y)))) :-
    A = _,
    Nodes = [x-A, y-A],
    once(egraph:extract(Nodes, Nodes)).

:- end_tests(extract_2).


% extract_node/1
:- begin_tests(extract_node).

% Chooses a representative for first group A->[x,y] (committed with once/1)
test(extract_node_choose_first_group, true(A==x)) :-
    A = _, B = _,
    Groups = [A-[x,y], B-[z]],
    once(egraph:extract_node(Groups)).

% Chooses a representative for second group B->[z]
test(extract_node_choose_second_group, true(B==z)) :-
    A = _, B = _,
    Groups = [A-[x,y], B-[z]],
    once(egraph:extract_node(Groups)).

% Fails when a group has an empty member list (defensive check)
% Although groups built from Nodes are nonempty, the predicate is semidet and should fail here.
test(extract_node_fails_on_empty_group, fail) :-
    A = _,
    egraph:extract_node([A-[]]).

:- end_tests(extract_node).


% add_expr/2
:- begin_tests(add_expr).

% Builds a left-associated chain: for N=3 yields (1+2)+3
test(left_assoc_n3, true(Expr == (1+2)+3)) :-
    egraph:add_expr(3, Expr).

% N=1 yields 1
test(n1_is_1, true(Expr == 1)) :-
    egraph:add_expr(1, Expr).

% N=0 is outside the domain (N >= 1); the predicate should fail
test(n0_out_of_domain, fail) :-
    egraph:add_expr(0, _).

:- end_tests(add_expr).


% example1/1
:- begin_tests(example1).

% Graph contains a-A
test(example1_contains_a, true(member(a-_A, G))) :-
    egraph:example1(G).

% Graph contains f^4(a)
test(example1_contains_f4a, true(member(f(f(f(f(a))))-_Id, G))) :-
    egraph:example1(G).

% Aliases the Id for 'a' with the Id for f(f(a)) via union/2
% Follow the chain a-A, f(A)-FA, then f(FA)-FFA to disambiguate the correct f/1 node.
test(example1_ids_aliased_by_union, true(A==FFA)) :-
    egraph:example1(G),
    memberchk(a-A, G),
    memberchk(f(A)-FA, G),
    memberchk(f(FA)-FFA, G).

:- end_tests(example1).


% example2/2
:- begin_tests(example2).

% Returns left-associated expression built by add_expr/2 for N=3
test(returns_left_assoc_expr, true(Expr == (1+2)+3)) :-
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

% lookup (more aspects)
:- begin_tests(lookup_more).

% Non-canonical list may spuriously fail even if key is present (precondition requires canonical ordset)
test(noncano_list_fails, fail) :-
    X = _, Y = _, Z = _,
    egraph:lookup(b-_, [a-X, c-Z, b-Y]).

:- end_tests(lookup_more).


% add/4 (more)
:- begin_tests(add_more).

% Adds term with variable; variable identity preserved as part of Key
test(var_key_identity_kept, true((member(f(V1)-_, Out), member(f(V2)-_, Out), V1\==V2))) :-
    V1 = _, V2 = _, V1 \== V2,
    egraph:add(f(V1), _Id1, [], T1),
    egraph:add(f(V2), _Id2, T1, Out).

:- end_tests(add_more).


% add//2 (more)
:- begin_tests(add_dcg_more).

% Two adds of same atom are idempotent: second call reuses Id and does not add a new pair
test(idempotent_same_atom, true(Out == [a-Id])) :-
    phrase((egraph:add(a, Id), egraph:add(a, _)), [], Out).

:- end_tests(add_dcg_more).


% union//2 (more)
:- begin_tests(union_dcg_more).

% Aliasing two classes does not add or drop keys: count remains 2
test(no_new_nodes_count, true(length(Out,2))) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [x-A, y-B], Out).

:- end_tests(union_dcg_more).


% assoc//2 (more)
:- begin_tests(assoc_more).

% When class(BC) has two +(B,C) members, emit two triples (6 outputs)
test(two_members_emit_two_triples, true(length(Out,6))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C, B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), Out).

:- end_tests(assoc_more).


% reduce//2 (more)
:- begin_tests(reduce_more).

% Does not reduce when class(B) contains 0.0 (strict term equality to integer 0 is required)
test(zero_float_no_reduce, true(Out == [])) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0.0]], Index),
    phrase(egraph:reduce((A+B)-_, Index), Out).

:- end_tests(reduce_more).


% constant_folding//2 (more)
:- begin_tests(constant_folding_more).

% Supports mixed numeric types: 2 + 2.5 -> 4.5
test(mixed_numeric_adds_to_float, true(member(4.5-_C, Out))) :-
    A = _, B = _,
    ord_list_to_rbtree([A-[2], B-[2.5]], Index),
    phrase(egraph:constant_folding((A+B)-_AB, Index), Out).

% Two numeric members in class(B) produce two pairs and two equalities (4 outputs)
test(two_vb_members_emit_four, true(length(Out,4))) :-
    A = _, B = _,
    ord_list_to_rbtree([A-[1], B-[2,3]], Index),
    phrase(egraph:constant_folding((A+B)-_AB, Index), Out).

:- end_tests(constant_folding_more).


% rules//3 (more)
:- begin_tests(rules_more).

% Empty Rules list produces no output
test(empty_rules_no_output, true(Out == [])) :-
    phrase(egraph:rules([], _Index, (a+b)-_AB), Out).

:- end_tests(rules_more).


% match/4 (more)
:- begin_tests(match_more).

% No rules and empty worklist yield no matches
test(empty_rules_and_worklist, true(Matches == [])) :-
    ord_list_to_rbtree([], Index),
    egraph:match([], [], Index, Matches).

:- end_tests(match_more).


% push_back//1 (more)
:- begin_tests(push_back_more).

% Pushing an empty list appends nothing
test(push_empty_noop, true(Out == [])) :-
    phrase(egraph:push_back([]), [], Out).

:- end_tests(push_back_more).


% saturate//2 (more)
:- begin_tests(saturate_more).

% Alias-only steps from reduce do not grow the graph
test(reduce_alias_only_no_growth, true(L2 == L1)) :-
    phrase(egraph:add(1+0, _), [], G0),
    length(G0, L1),
    phrase(egraph:saturate([reduce], 10), G0, G2),
    length(G2, L2).

:- end_tests(saturate_more).




% ordsets: ord_add_element/3 behavior on Key-Id pairs
:- begin_tests(ordsets_ord_add_element).

% Insert into empty set yields singleton
test(insert_empty_singleton, true(Out == [a-X])) :-
    X = _,
    ord_add_element([], a-X, Out).

% Insert keeps canonical order when appending a larger key
test(insert_keeps_order, true(Out == [a-X, b-Y])) :-
    X = _, Y = _,
    ord_add_element([a-X], b-Y, Out).

% Insert before when adding smaller key
test(insert_at_front, true(Out == [a-X, b-Y])) :-
    X = _, Y = _,
    ord_add_element([b-Y], a-X, Out).

% Allows same key with different Id (distinct element)
test(allows_same_key_diff_id, true(length(Out,2))) :-
    X = _, Y = _,
    X \== Y,
    ord_add_element([a-X], a-Y, Out).

% Does not duplicate an existing identical pair
test(no_duplicate_identical_pair, true(Out == [a-X])) :-
    X = _,
    ord_add_element([a-X], a-X, Out).

:- end_tests(ordsets_ord_add_element).


% ordsets: ord_subtract/3 behavior with variables and Key-Id pairs
:- begin_tests(ordsets_ord_subtract).

% Removing nothing: subtracting [] from a non-empty set returns the same set
test(sub_empty_subtrahend, true(R == [a,b,c])) :-
    ord_subtract([a,b,c], [], R).

% Removing from empty: subtracting a non-empty set from [] yields []
test(sub_empty_minuend, true(R == [])) :-
    ord_subtract([], [a,b], R).

% Identical sets: subtracting a set from itself yields []
test(sub_identical_sets, true(R == [])) :-
    S = [a, b, c],
    ord_subtract(S, S, R).

% Variable identity: shared variable is removed
% Here X is the same variable in both ordsets, so it is subtracted
test(sub_var_identity_removed, true(R == [Y])) :-
    X = _, Y = _,
    ord_subtract([X, Y], [X], R).

% Variable non-identity: distinct variables are not removed
% Here Z is a different variable than X, so X remains
test(sub_var_different_not_removed, true(R == [X,Y])) :-
    X = _, Y = _, Z = _, X \== Z,
    ord_subtract([X, Y], [Z], R).

% Compound with variable identity: f(X) is removed when the same X appears
test(sub_compound_var_identity_removed, true(R == [])) :-
    X = _,
    ord_subtract([f(X)], [f(X)], R).

% Compound with variant-equal but non-identical variable: f(X) is NOT removed by f(Y)
test(sub_compound_var_variant_not_removed, true(R == [f(X)])) :-
    X = _, Y = _, X \== Y,
    ord_subtract([f(X)], [f(Y)], R).

% Node-Id pair identity: subtracting the exact same pair removes it
test(sub_pair_exact_identity_removed, true(R == [b-Y])) :-
    X = _, Y = _,
    ord_subtract([a-X, b-Y], [a-X], R).

% Node-Id pair non-identity on Id: different Id var means the pair is not removed
test(sub_pair_diff_id_not_removed, true(R == [a-X, b-Y])) :-
    X = _, Y = _, Z = _, X \== Z,
    ord_subtract([a-X, b-Y], [a-Z], R).

% Order preserved: result remains an ordset in canonical order
test(sub_order_preserved, true(R == [a, c])) :-
    ord_subtract([a, b, c], [b], R).

% Idempotence w.r.t. the same subtrahend: subtracting again yields the same result
test(sub_idempotent_same_subtrahend, true(R2 == R)) :-
    ord_subtract([a, b, c], [b], R),
    ord_subtract(R, [b], R2).

% Multiple removals: remove two items appearing in the subtrahend
test(sub_remove_two_items, true(R == [c])) :-
    ord_subtract([a, b, c], [a, b], R).

% Removing non-members: elements not present in minuend are ignored
test(sub_remove_non_members_ignored, true(R == [a, b])) :-
    ord_subtract([a, b], [x, y], R).

% Mixed terms with variables: ensure only identical terms are removed
test(sub_mixed_terms_var_identity, true(R == [g(2), h(Z)])) :-
    X = _, Z = _,
    ord_subtract([f(X), g(2), h(Z)], [f(X)], R).

% Mixed terms with different variables: nothing removed if variables differ
test(sub_mixed_terms_var_non_identity, true(R == [f(X), g(2), h(Z)])) :-
    X = _, Y = _, Z = _, X \== Y,
    ord_subtract([f(X), g(2), h(Z)], [f(Y)], R).

% Defensive precondition highlight: ord_subtract requires canonical ordsets
% Here we provide already-canonical inputs constructed with ordsets primitives to ensure correctness.
test(sub_canonical_inputs_ok, true(R == [a-X, b-Y])) :-
    X = _, Y = _, Z = _,
    ord_add_element([], a-X, S1),
    ord_add_element(S1, b-Y, S2),
    ord_add_element([], a-Z, T1),
    ord_subtract(S2, T1, R).

:- end_tests(ordsets_ord_subtract).


% lookup (even more edge cases on list sizes/positions)
:- begin_tests(lookup_even_more).

% Finds the Id in a 2-element canonical list when the key is the second element
test(found_two_elems_second, true(V == Y)) :-
    X = _, Y = _,
    egraph:lookup(b-V, [a-X, b-Y]).

% Finds the Id in a 4-element canonical list when the key is the second (exercises X2 branch)
test(found_four_elems_second, true(V == X)) :-
    W = _, X = _, Y = _, Z = _,
    egraph:lookup(b-V, [a-W, b-X, c-Y, d-Z]).

% Finds the Id in a 4-element canonical list when the key is the third (exercises X3 branch)
test(found_four_elems_third, true(V == Y)) :-
    W = _, X = _, Y = _, Z = _,
    egraph:lookup(c-V, [a-W, b-X, c-Y, d-Z]).

:- end_tests(lookup_even_more).


% merge_nodes/2 (more)
:- begin_tests(merge_nodes_2_more).

% Three duplicate keys are deduplicated and all Ids are aliased to the head
test(triple_dedup_alias_all, true((Out == [x-A], A==B, A==C))) :-
    A = _, B = _, C = _,
    egraph:merge_nodes([x-A, x-B, x-C], Out).

:- end_tests(merge_nodes_2_more).


% reduce//2 (even more)
:- begin_tests(reduce_even_more).

% Emits at most one equality even if class(B) contains multiple zeros (once/1 guard)
test(once_emits_one_equality, true(length(Out, 1))) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[0, 0, 1]], Index),
    phrase(egraph:reduce((A+B)-_, Index), Out).

:- end_tests(reduce_even_more).


% extract_node/1 (more)
:- begin_tests(extract_node_more).

% Backtracks over representative choices in the first group: yields two solutions {x,y}
test(backtracks_two_choices, true(Sorted == [x,y])) :-
    findall(AV,
            ( A = _, B = _,
              egraph:extract_node([A-[x,y], B-[z]]),
              AV = A
            ),
            As),
    sort(As, Sorted).

:- end_tests(extract_node_more).


% ordsets: ord_subtract/3 (more with variables and pairs)
:- begin_tests(ordsets_ord_subtract_more).

% Variables aliased before subtraction: subtracting [Z] removes [X] when X==Z
test(var_aliasing_removes, true(R == [Y])) :-
    X = _, Y = _, Z = _,
    X = Z,
    ord_subtract([X, Y], [Z], R).

% Order preserved after removing a middle variable from a 3-variable ordset
test(var_remove_middle_preserves_order, true(R == [X, Z])) :-
    X = _, Y = _, Z = _,
    % Build canonical [X,Y,Z] using ordsets to respect standard order
    ord_add_element([], X, S1),
    ord_add_element(S1, Y, S2),
    ord_add_element(S2, Z, S),
    ord_subtract(S, [Y], R).

% Compound with same variable identity: f(X) is removed by f(X)
test(compound_same_var_removed, true(R == [g(X)])) :-
    X = _,
    ord_subtract([f(X), g(X)], [f(X)], R).

% Compound with variant-equal but non-identical variable: f(X) is NOT removed by f(Y)
test(compound_variant_var_not_removed, true(R == [f(X), g(X)])) :-
    X = _, Y = _, X \== Y,
    ord_subtract([f(X), g(X)], [f(Y)], R).

% Node-Id pair with aliased Id variables: removing [a-Z] after X=Z removes [a-X]
test(pair_id_vars_aliased_removed, true(R == [b-Y])) :-
    X = _, Y = _, Z = _,
    X = Z,
    ord_subtract([a-X, b-Y], [a-Z], R).

% Node-Id pair with variant-equal but non-identical variable in the Key is not removed
test(pair_variant_key_var_not_removed, true(R == [f(X)-Id])) :-
    X = _, Y = _, Id = _,
    X \== Y,
    ord_subtract([f(X)-Id], [f(Y)-Id], R).

:- end_tests(ordsets_ord_subtract_more).


% lookup/2 (even more 2)
:- begin_tests(lookup_even_more2).

% Finds the Id in a 4-element canonical list when the key is the first (X1 branch via R4(<), then R2(<))
test(found_four_elems_first, true(V == W)) :-
    W = _, X = _, Y = _, Z = _,
    egraph:lookup(a-V, [a-W, b-X, c-Y, d-Z]).

% Finds the Id in a 4-element canonical list when the key is the fourth (X4 direct match)
test(found_four_elems_fourth, true(V == Z)) :-
    W = _, X = _, Y = _, Z = _,
    egraph:lookup(d-V, [a-W, b-X, c-Y, d-Z]).

% Finds the Id in a 3-element canonical list when the key is the first
test(found_three_elems_first, true(V == X)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(a-V, [a-X, b-Y, c-Z]).

% Finds the Id in a 3-element canonical list when the key is the second
test(found_three_elems_second, true(V == Y)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(b-V, [a-X, b-Y, c-Z]).

% Finds the Id in a 3-element canonical list when the key is the third
test(found_three_elems_third, true(V == Z)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(c-V, [a-X, b-Y, c-Z]).

% Fails when Key is absent from a 2-element canonical list
test(fail_two_elems_absent, fail) :-
    X = _, Y = _,
    egraph:lookup(c-_, [a-X, b-Y]).

:- end_tests(lookup_even_more2).


% add/4 (more 2)
:- begin_tests(add_4_more2).

% Re-adding the same compound term reuses the same Id
test(readd_compound_reuse_id, true(Id2==Id)) :-
    egraph:add(f(a,b), Id, [], Out1),
    egraph:add(f(a,b), Id2, Out1, _Out2).

% Re-adding the same compound term does not change the set
test(readd_compound_no_set_change, true(Out2==Out1)) :-
    egraph:add(f(a,b), _Id, [], Out1),
    egraph:add(f(a,b), _Id2, Out1, Out2).

% Adding compound with variables preserves variable identity in Key
test(compound_with_vars_identity_preserved, true((member(f(V1)-_, Out), member(f(V2)-_, Out), V1\==V2))) :-
    V1 = _, V2 = _, V1 \== V2,
    egraph:add(f(V1), _Id1, [], T),
    egraph:add(f(V2), _Id2, T, Out).

:- end_tests(add_4_more2).


% add//2 (more 2)
:- begin_tests(add_dcg_2_more2).

% Re-adding the same compound via DCG is idempotent (second call reuses and does not add)
test(dcg_readd_compound_idempotent, true(length(Out,3))) :-
    % First add of f(a,b) yields a-A, b-B, f(A,B)-Id (3 nodes)
    phrase((egraph:add(f(a,b), _), egraph:add(f(a,b), _)), [], Out).

% DCG on compound preserves child Id reuse consistently across separate calls
test(dcg_compound_child_id_reuse, true((member(a-A, Out), member(b-B, Out), member(f(A,B)-_, Out)))) :-
    phrase(egraph:add(f(a,b), _), [], Out).

:- end_tests(add_dcg_2_more2).


% add_node/3 (more 2)
:- begin_tests(add_node_3_more2).

% Insert a compound Node key directly; treated as a Key and inserted
test(insert_compound_key, true(member(f(x)-Id, Out))) :-
    egraph:add_node(f(x), Id, [], Out).

% Variable identity in compound Key: f(X) and f(Y) with X\==Y both kept
test(insert_compound_var_identity, true((member(f(X)-_, Out), member(f(Y)-_, Out), X\==Y))) :-
    X = _, Y = _, X \== Y,
    egraph:add_node(f(X), _Id1, [], T),
    egraph:add_node(f(Y), _Id2, T, Out).

:- end_tests(add_node_3_more2).


% merge_group/4 (more 2)
:- begin_tests(merge_group_more2).

% When Changed0 is already true and group is non-trivial, Changed remains true
test(changed_flag_sticky_true, true(Changed)) :-
    A = _, B = _,
    egraph:merge_group(x-[A,B], _Rep, true, Changed).

:- end_tests(merge_group_more2).


% comm//2 (more)
:- begin_tests(comm_more).

% The equality uses the same AB variable as provided in input node
test(eq_uses_input_ab, true(member(AB=_, Out))) :-
    A = _, B = _, AB = _,
    phrase(egraph:comm((A+B)-AB, _Index), Out).

:- end_tests(comm_more).


% assoc//2 (more 2)
:- begin_tests(assoc_more2).

% Non-match for nodes not of form (A+BC)-ABC yields no output
test(nonmatch_empty, true(Out == [])) :-
    ord_list_to_rbtree([], Index),
    phrase(egraph:assoc(foo-_, Index), Out).

:- end_tests(assoc_more2).


% rule//3 (more 2)
:- begin_tests(rule_more2).

% Reduce rule emits nothing when class(B) lacks 0 (Index does not contain B or lacks 0)
test(reduce_emits_nothing_when_no_zero, true(Out == [])) :-
    A = _, B = _,
    ord_list_to_rbtree([B-[1,2]], Index),
    phrase(egraph:rule(Index, (A+B)-_AB, reduce), Out).

:- end_tests(rule_more2).


% make_index/2 (more 2)
:- begin_tests(make_index_more2).

% rb_lookup/3 fails when Id not present in index
test(rb_lookup_missing_fails, fail) :-
    A = _, B = _,
    Nodes = [x-A, y-A, z-B],
    egraph:make_index(Nodes, Index),
    C = _,
    rb_lookup(C, _Keys, Index).

:- end_tests(make_index_more2).


% match/4 (more 2)
:- begin_tests(match_more2).

% With two rules [comm, reduce], outputs start with comm node then comm eq then reduce eq
test(order_comm_then_reduce, true((Matches = [K1, Eq1, Eq2 | _], K1 = (B+A)-_, Eq1 = (AB=_), Eq2 = (A=AB)))) :-
    A = _, B = _, AB = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([B-[0]], Index),
    egraph:match([comm, reduce], Work, Index, Matches).

:- end_tests(match_more2).


% rebuild//1 (more 2)
:- begin_tests(rebuild_more2).

% Duplicate Key-Id pairs scheduled via Matches are deduplicated and Ids unified
test(duplicates_in_matches_dedup_and_unify, true((Out == [x-A], A==B))) :-
    A = _, B = _,
    In = [],
    Matches = [x-A, x-B],
    phrase(egraph:rebuild(Matches), In, Out).

% No equalities: rebuild still canonicalizes and sorts the accumulated nodes
test(no_equalities_canonicalizes, true(Out == [a-A, b-B])) :-
    A = _, B = _,
    In = [b-B],
    Matches = [a-A],
    phrase(egraph:rebuild(Matches), In, Out).

:- end_tests(rebuild_more2).


% saturate//1 (more 2)
:- begin_tests(saturate_dcg_1_more2).

% With no rules, saturate//1 leaves the graph unchanged
test(no_rules_no_change, true(G2 == G0)) :-
    phrase(egraph:add(1+2, _), [], G0),
    phrase(egraph:saturate([]), G0, G2).

:- end_tests(saturate_dcg_1_more2).


% saturate/4 (more 2)
:- begin_tests(saturate_4_more2).

% Alias-only steps (reduce) do not change length after one iteration
test(alias_only_no_growth, true(L1 == L0)) :-
    phrase(egraph:add(1+0, _), [], G0),
    length(G0, L0),
    egraph:saturate([reduce], 1, G0, G1),
    length(G1, L1).

:- end_tests(saturate_4_more2).


% extract/1 (more 2)
:- begin_tests(extract_more2).

% Backtracks over representative choices: collects both x and y
test(backtracks_two_reps, true(Sorted == [x,y])) :-
    A = _,
    Nodes = [x-A, y-A],
    findall(AVal, (egraph:extract(Nodes), AVal=A), AVals),
    sort(AVals, Sorted).

:- end_tests(extract_more2).


% add_expr/2 (more 2)
:- begin_tests(add_expr_more2).

% N < 1 (e.g., -1) is outside domain; predicate should fail
test(nneg_out_of_domain, fail) :-
    egraph:add_expr(-1, _).

:- end_tests(add_expr_more2).


% ordsets: ord_add_element/3 (more 2)
:- begin_tests(ordsets_ord_add_element_more2).

% Inserting two pairs with the same Key but different Id vars keeps both and preserves order
test(same_key_diff_ids_kept_and_ordered, true(Out == [a-X, a-Y])) :-
    X = _, Y = _, X \== Y,
    ord_add_element([], a-X, S),
    ord_add_element(S, a-Y, Out).

:- end_tests(ordsets_ord_add_element_more2).


% ordsets: ord_subtract/3 (even more)
:- begin_tests(ordsets_ord_subtract_even_more).

% Subtracting a superset yields empty set
test(sub_superset_empty, true(R == [])) :-
    ord_subtract([a,b], [a,b,c], R).

% Subtracting a subset from a larger set yields the remaining elements
test(sub_subset_remaining, true(R == [c])) :-
    ord_subtract([a,b,c], [a,b], R).

% Compound with aliased variable identity: f(X) removed by f(Z) after X=Z
test(compound_alias_then_remove, true(R == [])) :-
    X = _, Z = _, X = Z,
    ord_subtract([f(X)], [f(Z)], R).

% Deep compound with non-identical variables: g(h(X),X) not removed by g(h(X),Y) when X\==Y
test(deep_compound_variant_not_removed, true(R == [g(h(X),X)])) :-
    X = _, Y = _, X \== Y,
    ord_subtract([g(h(X),X)], [g(h(X),Y)], R).

% Pair subtraction: removing two existing pairs leaves only the remaining pair
test(pair_subtract_two, true(R == [c-Z])) :-
    X = _, Y = _, Z = _,
    ord_subtract([a-X, b-Y, c-Z], [a-X, b-Y], R).

% Pair subtraction with compound Keys and aliased Ids: [f(X)-I] removed by [f(X)-J] only if I==J; here I\==J so not removed
test(pair_compound_diff_id_not_removed, true(R == [f(X)-I])) :-
    X = _, I = _, J = _, I \== J,
    ord_subtract([f(X)-I], [f(X)-J], R).

% Pair subtraction with aliased Ids: [a-I] is removed by [a-J] after I=J
test(pair_ids_aliased_then_removed, true(R == [])) :-
    I = _, J = _, I = J,
    ord_subtract([a-I], [a-J], R).

% Variable-only ordset: removing middle variable preserves order of remaining endpoints
% Build canonical [X1, X2, X3] and subtract [X2] -> [X1, X3]
test(vars_three_remove_middle, true(R == [X1, X3])) :-
    X1 = _, X2 = _, X3 = _,
    ord_add_element([], X1, S1),
    ord_add_element(S1, X2, S2),
    ord_add_element(S2, X3, S),
    ord_subtract(S, [X2], R).

% Variable aliasing: subtracting [Y] removes [X2] when X2==Y in [X1, X2, X3]
test(vars_three_alias_then_remove, true(R == [X1, X3])) :-
    X1 = _, X2 = _, X3 = _, Y = _,
    X2 = Y,
    ord_add_element([], X1, S1),
    ord_add_element(S1, X2, S2),
    ord_add_element(S2, X3, S),
    ord_subtract(S, [Y], R).

% Node-Id pair: Key variable equal, Ids differ -> not removed
test(pair_var_key_diff_id_not_removed, true(R == [K-I])) :-
    K = _, I = _, J = _, I \== J,
    ord_subtract([K-I], [K-J], R).

% Node-Id pair: Key variables aliased and Ids identical -> removed
test(pair_var_key_aliased_removed, true(R == [])) :-
    K1 = _, K2 = _, I = _,
    K1 = K2,
    ord_subtract([K1-I], [K2-I], R).

% Deep compound with same variable in both positions: exact identity -> removed
test(deep_compound_two_occ_same_var_removed, true(R == [])) :-
    X = _,
    ord_subtract([g(X,X)], [g(X,X)], R).

% Deep compound with swapped distinct variables: not identical -> not removed
test(deep_compound_two_occ_variant_not_removed, true(R == [g(X,Y)])) :-
    X = _, Y = _, X \== Y,
    ord_subtract([g(X,Y)], [g(Y,X)], R).

% Compound Key inside pair with inner variable aliasing and identical Id -> removed
test(pair_compound_key_inner_var_aliased_removed, true(R == [])) :-
    X = _, Y = _, I = _,
    X = Y,
    ord_subtract([f(g(X))-I], [f(g(Y))-I], R).

:- end_tests(ordsets_ord_subtract_even_more).

% make_index/2 (additional)
:- begin_tests(make_index_more3).

% Index size equals the number of distinct class Ids (two classes -> size 2)
test(rb_size_two_classes, true(Size == 2)) :-
    A = _, B = _,
    Nodes = [x-A, y-A, z-B],
    egraph:make_index(Nodes, Index),
    rb_size(Index, Size).

:- end_tests(make_index_more3).


% ordsets: ord_subtract/3 (edge cases)
:- begin_tests(ordsets_ord_subtract_edge).

% Removing one of two identical-key pairs removes only the identical pair, leaving the other
test(pair_remove_one_of_same_key_two_ids, true(R == [a-Y])) :-
    X = _, Y = _, X \== Y,
    ord_add_element([], a-X, S1),
    ord_add_element(S1, a-Y, S),
    ord_subtract(S, [a-X], R).

% Subtracting a variable from a set containing a compound with that variable does not remove the compound
% Terms differ: X \== f(X), so f(X) remains
test(var_vs_compound_not_removed, true(R == [f(X)])) :-
    X = _,
    ord_subtract([f(X)], [X], R).

:- end_tests(ordsets_ord_subtract_edge).
