:- use_module(egraph3).
:- use_module(library(plunit)).
:- use_module(library(rbtrees)).

% lookup/2
:- begin_tests(lookup).

% Ensure lookup finds the Id in a 1-element list
test(found_1elem, true(V == X)) :-
    X = _,
    egraph:lookup(a-V, [a-X]).

% Ensure lookup finds the Id in a 2+ element canonical list
test(found_multi, true(V == Y)) :-
    X = _, Y = _, Z = _,
    egraph:lookup(b-V, [a-X, b-Y, c-Z]).

% Ensure lookup fails on empty list
test(fail_empty, fail) :-
    egraph:lookup(a-_, []).

:- end_tests(lookup).


% add//2 and add/4
:- begin_tests(add).

% Add an atom; second add reuses the same Id and does not change the set
test(atom_reuse, true((Id2==Id, Out2==Out1))) :-
    egraph:add(a, Id, [], Out1),
    egraph:add(a, Id2, Out1, Out2).

% Add a compound term; children are added left-to-right and node uses child Ids
test(compound_children, true((
    member(a-A, Out),
    member(b-B, Out),
    member(f(A,B)-Id, Out)
))) :-
    egraph:add(f(a,b), Id, [], Out).

% DCG form: add//2 builds nodes via phrase/3
test(dcg_add_atom, true(Out == [a-Id])) :-
    phrase(egraph:add(a, Id), [], Out).

:- end_tests(add).


% add_node/3 and add_node/4
:- begin_tests(add_node).

% Inserting a new node produces it with a fresh Id
test(insert_new, true((member(x-Id, Out), length(Out,1)))) :-
    egraph:add_node(x, Id, [], Out).

% Re-adding an existing node reuses Id and is a no-op on the set
test(reuse_existing, true((Out==In, Id==X))) :-
    X = _,
    In = [x-X],
    egraph:add_node(x, Id, In, Out).

% Pair form delegates to add_node/4 and uses the provided Id
test(pair_form, true(member(y-Y, Out))) :-
    egraph:add_node(y-Y, [x-X], Out),
    X = _.

:- end_tests(add_node).


% union//2 and union/4
:- begin_tests(union).

% Union aliases Ids and preserves canonical ordset semantics
test(alias_and_merge, true((
    A==B,
    member(x-A, Out),
    member(y-A, Out)
))) :-
    A = _, B = _,
    phrase(egraph:union(A, B), [x-A, y-B], Out).

% Union inside a build pipeline
test(dcg_pipeline_alias, true(A==FFA)) :-
    phrase((egraph:add(a, A),
            egraph:add(f(f(a)), FFA),
            egraph:union(A, FFA)), [], _Out).

:- end_tests(union).


% merge_nodes//0 and merge_nodes/2
:- begin_tests(merge_nodes).

% DCG form is a no-op on an empty set
test(dcg_empty_noop, true(Out == [])) :-
    phrase(egraph:merge_nodes, [], Out).

% Duplicate keys are deduplicated and Ids are aliased
test(dedup_and_alias, true((Out == [x-A], A==B))) :-
    A = _, B = _,
    egraph:merge_nodes([x-A, x-B], Out).

% Id aliasing can instantiate variables inside Keys, collapsing collisions
test(alias_instantiates_keys, true((member(f(A)-FA, Out), FB==FA))) :-
    A = _, B = _, FA = _, FB = _,
    In = [a-A, b-B, f(A)-FA, f(B)-FB],
    A = B,
    egraph:merge_nodes(In, Out).

:- end_tests(merge_nodes).


% merge_group/4
:- begin_tests(merge_group).

% Non-trivial group unifies all Ids with representative and sets Changed=true
test(group_merge_changes, true((Rep==A, B==A, Changed))) :-
    A = _, B = _,
    egraph:merge_group(x-[A,B], x-Rep, false, Changed).

% Single-element group preserves Changed flag
test(group_single_nochange, true((Rep==A, Changed0==Changed))) :-
    A = _, Changed0 = false,
    egraph:merge_group(x-[A], x-Rep, Changed0, Changed).

:- end_tests(merge_group).


% comm//2
:- begin_tests(comm).

% Emits commuted variant and equality for +(A,B)
test(comm_emits, true((
    Out = [B+A-BA, AB=BA],
    var(BA), var(AB)
))) :-
    A = _, B = _, AB = _,
    phrase(egraph:comm((A+B)-AB, _Index), [], Out).

% Non-match produces no output
test(comm_nomatch_empty, true(Out == [])) :-
    phrase(egraph:comm(foo-Id, _Idx), [], Out),
    Id = _.

:- end_tests(comm).


% assoc//2 and assoc_//3
:- begin_tests(assoc).

% Emits associativity transforms when class(BC) includes a +(B,C) member
test(assoc_emits, true((
    Out = [A+B-AB, AB+C-ABC_, ABC=ABC_],
    var(AB), var(ABC_), var(ABC)
))) :-
    A = _, B = _, C = _, BC = _, ABC = _,
    ord_list_to_rbtree([BC-[B+C]], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), [], Out).

% No mapping for BC in Index => no output
test(assoc_nomap_empty, true(Out == [])) :-
    A = _, BC = _, ABC = _,
    ord_list_to_rbtree([], Index),
    phrase(egraph:assoc((A+BC)-ABC, Index), [], Out).

% Helper assoc_//3 skips non-+(B,C) members and emits for matching ones
test(assoc_helper_filters, true(Out == [a+b-AB, AB+c-ABC_, ABC=ABC_])) :-
    AB = _, ABC = _,
    phrase(egraph:assoc_([foo, b+c], a, ABC), [], Out).

:- end_tests(assoc).


% reduce//2
:- begin_tests(reduce).

% If class(B) contains 0, reduce A+B to A=AB
test(reduce_has_zero, true(Out == [A=AB])) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[0, 1]], Index),
    phrase(egraph:reduce(A+B-AB, Index), [], Out).

% If class(B) lacks 0, no reduction
test(reduce_no_zero, true(Out == [])) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[1, 2]], Index),
    phrase(egraph:reduce(A+B-AB, Index), [], Out).

:- end_tests(reduce).


% constant_folding//2, constant_folding_a//4, constant_folding_b//4
:- begin_tests(constant_folding).

% Folds numeric sums; skips non-numeric class members
test(fold_numeric_only, true((
    sort(Out, Sorted),
    Sorted == [5-C1, C1=AB]
))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([A-[2, foo], B-[3]], Index),
    phrase(egraph:constant_folding((A+B)-AB, Index), [], Out).

% Helper constant_folding_a//4 filters by number/1
test(fold_a_filters, true((
    sort(Out, Sorted),
    Sorted == [5-C, C=AB, 9-C2, C2=AB]
))) :-
    B = _, AB = _,
    ord_list_to_rbtree([B-[3, 7]], Index),
    phrase(egraph:constant_folding_a([2, foo], B, AB, Index), [], Out).

% Helper constant_folding_b//4 filters VB by number/1
test(fold_b_filters, true(Out == [5-C, C=AB])) :-
    AB = _,
    phrase(egraph:constant_folding_b([3, foo], 2, AB, _Index), [], Out).

:- end_tests(constant_folding).


% rules//3 and rule//3
:- begin_tests(rules).

% rules//3 applies each rule in order and appends outputs
test(rules_apply_order, true((
    member(b+a-BA, Out),
    member(AB=BA, Out),
    member(A=AB, Out)
))) :-
    A = _, B = _, AB = _,
    ord_list_to_rbtree([B-[0]], Index),
    Rules = [comm, reduce],
    phrase(egraph:rules(Rules, Index, (A+B)-AB), [], Out).

% rule//3 wraps a single DCG rule
test(rule_wrapper_comm, true(Out == [B+A-BA, AB=BA])) :-
    A = _, B = _, AB = _,
    phrase(egraph:rule(_Index, (A+B)-AB, comm), [], Out).

:- end_tests(rules).


% make_index/2
:- begin_tests(make_index).

% Builds rbtree Id -> [Keys] from canonical nodes
test(index_build, true((
    rb_lookup(A, KeysA, Index),
    sort(KeysA, SortedA),
    SortedA == [x,y],
    rb_lookup(B, KeysB, Index),
    KeysB == [z]
))) :-
    A = _, B = _,
    Nodes = [x-A, y-A, z-B],
    egraph:make_index(Nodes, Index).

:- end_tests(make_index).


% match/4
:- begin_tests(match).

% match/4 runs rules over worklist using Index
test(match_comm, true((
    member(b+a-BA, Matches),
    member(AB=BA, Matches)
))) :-
    A = _, B = _, AB = _,
    Work = [(A+B)-AB],
    ord_list_to_rbtree([], Index),
    egraph:match([comm], Work, Index, Matches).

:- end_tests(match).


% push_back//1
:- begin_tests(push_back).

% push_back appends its list to the DCG output
test(push_appends, true(Out == [a,b])) :-
    phrase(egraph:push_back([a,b]), [], Out).

:- end_tests(push_back).


% rebuild//1
:- begin_tests(rebuild).

% rebuild performs Id aliasing for (=)/2, enqueues nodes, and canonicalizes
test(rebuild_alias_and_enqueue, true((
    A==B,
    member(x-A, Out),
    member(y-A, Out),
    member(z-C, Out)
))) :-
    A = _, B = _, C = _,
    In = [x-A, y-B],
    Matches = [A=B, z-C],
    phrase(egraph:rebuild(Matches), In, Out).

:- end_tests(rebuild).


% saturate//1, saturate//2, saturate/4
:- begin_tests(saturate).

% saturate//1 reaches a length fixpoint after adding commuted variant
test(sat_fixpoint_comm, true((
    length(G1, L1),
    length(G2, L2),
    L2 is L1 + 1,
    member(2+1-AB, G2),
    member(1+2-AB, G2)
))) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    phrase(egraph:saturate([comm]), G0, G2),
    length(G0, L1).

% saturate//2 with MaxSteps=0 leaves graph unchanged
test(sat_zero_steps, true(G == G0)) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    phrase(egraph:saturate([comm], 0), G0, G).

% saturate/4 one step grows by exactly one node for comm rule
test(sat_one_step_driver, true(length(G1, L0p1))) :-
    AB = _,
    phrase(egraph:add(1+2, AB), [], G0),
    egraph:saturate([comm], 1, G0, G1),
    length(G0, L0),
    L0p1 is L0 + 1.

:- end_tests(saturate).


% unif/1
:- begin_tests(unif).

% Unifies arguments when given an equality term
test(unif_does_unify, true(A==B)) :-
    A = _, B = _,
    egraph:unif(A=B).

% Fails for non-equality term
test(unif_fails_non_eq, fail) :-
    egraph:unif(foo).

:- end_tests(unif).


% extract/1, extract//0, extract/2, extract_node/1
:- begin_tests(extract).

% extract/1 aliases Ids to a representative Key (one per class)
test(extract_aliases_ids, true((A==X ; A==Y))) :-
    A = _, X = x, Y = y,
    Nodes = [x-A, y-A],
    egraph:extract(Nodes).

% extract//0 DCG wrapper succeeds and aliases through Nodes
test(extract_dcg, true((A==x ; A==y))) :-
    A = _,
    Nodes = [x-A, y-A],
    phrase(egraph:extract, Nodes, Nodes).

% extract/2 semidet form
test(extract_semidet, true((A==x ; A==y))) :-
    A = _,
    Nodes = [x-A, y-A],
    egraph:extract(Nodes, Nodes).

% extract_node/1 chooses a member per group; semidet over empty
test(extract_node_groups, true((A==x, B==z))) :-
    A = _, B = _,
    Groups = [A-[x,y], B-[z]],
    once(egraph:extract_node(Groups)).

:- end_tests(extract).


% add_expr/2
:- begin_tests(add_expr).

% Builds right-associated sum 1+2+...+N
test(right_assoc, true(Expr == 1+(2+3))) :-
    egraph:add_expr(3, Expr).

% N=1 yields 1
test(n1_is_1, true(Expr == 1)) :-
    egraph:add_expr(1, Expr).

:- end_tests(add_expr).


% example1/1
:- begin_tests(example1).

% Graph contains f^4(a) and a, and their Ids have been unioned (aliased)
test(example1_props, true((
    member(a-A, G),
    member(f(f(f(f(a))))-Id, G),
    A==Id
))) :-
    egraph:example1(G).

:- end_tests(example1).


% example2/2
:- begin_tests(example2).

% Returns the built Expr; side effects are timing/printing which we ignore
test(example2_expr, true(Expr == 1+(2+3))) :-
    with_output_to(string(_), egraph:example2(3, Expr)).

:- end_tests(example2).


% example3/3
:- begin_tests(example3).

% For N=1 and Expr=1, the only extracted result is 1
test(example3_n1, true(Rs == [1])) :-
    findall(R, egraph:example3(1, 1, R), Rs).

% For N=2 and Expr=1+2, one possible extracted result is 3
test(example3_n2_has_3, true(member(3, Rs))) :-
    egraph:add_expr(2, Expr),
    findall(R, egraph:example3(2, Expr, R), Rs).

:- end_tests(example3).
