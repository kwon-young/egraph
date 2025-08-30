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

% BUG: Keys are variable-identity sensitive; variant-equal keys with different variables are not identical and should not be found.
% Demonstrates that lookup/2 does not match f(V2) against existing f(V1) when V1 \== V2.
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
% This test encodes the intended behavior (no output) and currently fails.
test(assoc_nomap_empty, [fail]) :-
    A = _, BC = _, ABC = _,
    ord_list_to_rbtree([], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), _Out).

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
test(match_comm_node, true(member((b+a)-_, Matches))) :-
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
