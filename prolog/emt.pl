:- module(emt, [lookup/2, add_term//2, add_node//3, rebuild//1,
                with_theory//2]).

/** <module> E-graph modulo theory (EMT) sketch

Minimal E-graph implementation using Prolog variables as e-class ids.
This is a pedagogical re-implementation of egraph.pl using the
E-graph Modulo Theory approach, starting with AC theory support.

The EMT state is a list of Theory-Data pairs, e.g. [egraph-List].
Each theory manages its own data structure.

Design note: e-class ids are Prolog variables, merged by unification.
Since we cannot mutate an existing node entry in place, congruence
closure is done in *batch*: each theory's node list is sorted
(`sort` for egraph to dedup identical nodes, `msort` for ac to
canonize multiset nodes keeping duplicates) and grouped by canonical
key so that congruent nodes collapse together (see rebuild//1 and
merge_groups//2), rather than via an incremental union-find.

Notation recap:

  * **DCG (`-->`)** threads an implicit state pair `S0,S` through a
    sequence of operations (not for parsing). `phrase(G, In, Out)`
    runs it; `{G}` is a plain Prolog goal that skips the state.
  * **SSU (`==>`)** is one-sided, committing pattern matching: the
    head matches without instantiating the caller; on match it
    commits (no backtracking to later clauses).
  * **`Head, Cond ==> Body`** combines both: `Cond` may contain DCG
    goals (state-threaded) and `{G}` goals (plain). First matching
    clause commits. See add_term//2, ac_flatten//2.
  * **Ordsets as multisets.**  We abuse `library(ordsets)` on
    `msort`-ed lists (which keep duplicates) to get sorted multiset
    ops: `ord_union`~multiset sum, `ord_subtract`~difference,
    `ord_intersect`/`ord_subset`~overlap/containment.
*/

:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(library(dcg/high_order)).

lookup(Node-Class, [N-C | _]), Node == N =>
   Class = C.
lookup(Node-Class, [_ | L]) =>
   lookup(Node-Class, L).
lookup(_, []) => fail.

with_theory(Theory, Goal, In, Out) :-
    selectchk(Theory-DataIn, In, Theory-DataOut, Out),
    call(Goal, DataIn, DataOut).

add_term(A+B, Id) ==>
    { ac_flatten(+, A+B, Args, []) },
    add_terms(Args, Ids),
    { msort(Ids, Sort) },
    add_node(ac, node(+, Sort), Id).
add_term(Term, Id), compound(Term) ==>
   { compound_name_arguments(Term, F, Args) },
   add_terms(Args, Ids),
   { compound_name_arguments(Node, F, Ids) },
   add_node(egraph, Node, Id).
add_term(Term, Id) ==>
   add_node(egraph, Term, Id).

add_terms([], []) --> [].
add_terms([Term | Terms], [Id | Ids]) -->
   add_term(Term, Id),
   add_terms(Terms, Ids).

add_node(Theory, Node, Id) -->
   with_theory(Theory, add_node(Node, Id)).

add_node(Node, Id, In, Out) :-
    (  lookup(Node-Id, In)
    -> Out = In
    ;  ord_add_element(In, Node-Id, Out)
    ).

ac_flatten(F, Term), compound(Term), compound_name_arguments(Term, F, Args) ==>
    sequence(ac_flatten(F), Args).
ac_flatten(_, Arg) ==>
    [Arg].

rebuild([A=B | Unifs]) -->
    { A = B },
    rebuild(Unifs).
rebuild([]) -->
   with_theory(egraph, sort),
   with_theory(ac, maplist(ac_canonize_node)),
   congruence_closure(Unifs),
   (   { Unifs == [] }
   ->  []
   ;   rebuild(Unifs)
   ).

ac_canonize_node(node(F, Ids)-C, node(F, Sort)-C) :-
    msort(Ids, Sort).

congruence_closure(Unifs, In, Out) :-
    foldl(rebuild_groups, In, Out, Unifs, UnifsAC),
    with_theory(ac, ac_closure(UnifsAC), Out, _).
rebuild_groups(Theory-In, Theory-Out) -->
    { group_pairs_by_key(In, Groups) },
    merge_groups(Groups, Out).

merge_groups([], []) --> [].
merge_groups([Node-[Id | Ids] | Groups], [Node-Id | Out]) -->
    sequence(merge_id(Id), Ids),
    merge_groups(Groups, Out).
merge_id(A, B) --> [A=B].

ac_closure(Unifs, Nodes, Nodes) :-
    maplist(ac_node_rule, Nodes, Rules),
    phrase(critical_pairs(Rules), Worklist),
    phrase(ac_closure(Worklist, Rules), Unifs).
ac_closure([], _Rules) --> [].
ac_closure([C1-C2 | Worklist], Rules) -->
    { debug(ac_closure, "ac_closure", []) },
    {   ac_canonize_rule(Rules, C1, T1),
        ac_canonize_rule(Rules, C2, T2)
    },
    (   { T1 == T2 }
    ->  ac_closure(Worklist, Rules)
    ;   { reverse_grevlex(T1, T2, NewRule) },
        { phrase((
            interreduce(Rules, NewRule, RemainingRules),
            critical_pairs(Rules, NewRule)
          ), NewWorklist, Worklist) },
        (   { T1 = [A], T2 = [B] }
        ->  [A=B]
        ;   []
        ),
        ac_closure(NewWorklist, [NewRule | RemainingRules])
    ).

interreduce([], _, []) --> [].
interreduce([L2-R2 | Rules], L1-R1, RemainingRules) -->
    (   { ord_subset(L1, L2) }
    ->  [L2-R2],
        { R = RemainingRules }
    ;   { RemainingRules = [L2-R2 | R] }
    ),
    interreduce(Rules, L1-R1, R).

reverse_grevlex(T1, T2, Rule) :-
    length(T1, L1),
    length(T2, L2),
    compare(O, L1, L2),
    (   O == (>)
    ->  Rule = T1-T2
    ;   O == (<)
    ->  Rule = T2-T1
    ;   reverse(T1, R1),
        reverse(T2, R2),
        lex_order(R1, R2, Order),
        (   Order == (>)
        ->  Rule = T1-T2
        ;   Rule = T2-T1
        )
    ).
lex_order([A | T1], [B | T2], Order) :-
    compare(O, A, B),
    (   O == (=)
    ->  lex_order(T1, T2, Order)
    ;   O = Order
    ).

critical_pairs([]) --> [].
critical_pairs([Rule | Rules]) -->
    critical_pairs(Rules, Rule),
    critical_pairs(Rules).
critical_pairs([], _) --> [].
critical_pairs([L2-R2 | Rules], L1-R1) -->
    (   { ord_intersect(L1, L2) }
    ->  {   ord_union(L1, L2, Peak),
            apply_rule(L1-R1, Peak, C1),
            apply_rule(L2-R2, Peak, C2)
        },
        [C1-C2]
    ;   []
    ),
    critical_pairs(Rules, L1-R1).

ms_union(A, B, C) :-
    append(A, B, L),
    msort(L, C).

ac_canonize_rule(Rules, T1, T) :-
    ac_canonize_rule(Rules, Rules, T1, T).
ac_canonize_rule([], _, T, T).
ac_canonize_rule([Left-Right | Rules], AllRules, T1, T) :-
    (   ord_subset(Left, T1)
    ->  apply_rule(Left-Right, T1, T2),
        ac_canonize_rule(AllRules, T2, T)
    ;   ac_canonize_rule(Rules, T1, T)
    ).

apply_rule(Left-Right, T1, T) :-
    ord_subtract(T1, Left, T2),
    ms_union(T2, Right, T).

ac_node_rule(node(_F, Ids)-C, Ids-[C]).

:- begin_tests(emt_lookup).

test(head_match, true(C == 1)) :-
    lookup(a-C, [a-1]).

test(tail_match, true(C == 2)) :-
    lookup(f(x)-C, [g-0, f(x)-2]).

test(not_present, fail) :-
    lookup(missing-_, [a-1]).

test(identity_distinguishes_order, fail) :-
    X = a, Y = b,
    lookup(f(X, Y)-_, [f(Y, X)-_]).

:- end_tests(emt_lookup).

:- begin_tests(emt_add_node).

test(atomic_insert) :-
    phrase(add_node(egraph, a, Id), [egraph-[]], Out),
    Out == [egraph-[a-Id]].

test(sorted_insertion) :-
    phrase(( add_node(egraph, b, _),
             add_node(egraph, a, _)
          ), [egraph-[]], Out),
    Out =@= [egraph-[a-_, b-_]].

test(idempotent_reinsert, true(Id1 == Id2)) :-
    A = x, B = y,
    phrase(( add_node(egraph, f(A, B), Id1),
             add_node(egraph, f(A, B), Id2)
          ), [egraph-[]], Out),
    Out == [egraph-[f(A, B)-Id1]].

test(shared_args_dedup) :-
    A = x,
    phrase(add_node(egraph, h(A, A), _), [egraph-[]], Out),
    Out =@= [egraph-[h(A, A)-_]].

:- end_tests(emt_add_node).

:- begin_tests(emt_add_term).

test(atomic_term) :-
    phrase(add_term(atom, Id), [egraph-[]], Out),
    Out == [egraph-[atom-Id]].

test(atomic_distinct) :-
    phrase(( add_term(a, _),
             add_term(b, _)
          ), [egraph-[]], Out),
    Out =@= [egraph-[a-_, b-_]].

test(atomic_reuse, true(Id1 == Id2)) :-
    phrase(( add_term(a, Id1),
             add_term(a, Id2)
          ), [egraph-[]], Out),
    Out == [egraph-[a-Id1]].

test(compound_term) :-
    phrase(add_term(f(a, b), Id), [egraph-[]], Out),
    Out =@= [egraph-[a-A, b-B, f(A, B)-Id]].

:- end_tests(emt_add_term).

:- begin_tests(emt_ac_flatten).

test(two_args) :-
    phrase(ac_flatten(+, a+b), Args),
    Args == [a, b].

test(nested_right) :-
    phrase(ac_flatten(+, a+(b+c)), Args),
    Args == [a, b, c].

test(nested_left) :-
    phrase(ac_flatten(+, (a+b)+c), Args),
    Args == [a, b, c].

test(deep_nesting) :-
    phrase(ac_flatten(+, ((a+b)+c)+(d+e)), Args),
    Args == [a, b, c, d, e].

test(non_ac_functor_stops) :-
    phrase(ac_flatten(+, a+f(b,c)), Args),
    Args == [a, f(b, c)].

:- end_tests(emt_ac_flatten).

:- begin_tests(emt_add_ac).

test(add_ac_term) :-
    phrase(add_term(a+b, Id), [egraph-[], ac-[]], Out),
    Out =@= [egraph-[a-A, b-B], ac-[node(+, [A, B])-Id]].

test(ac_congruence, true(Id1 == Id2)) :-
    phrase(( add_term(a+b, Id1),
             add_term(b+a, Id2)
          ), [egraph-[], ac-[]], Out),
    Out =@= [egraph-[a-A, b-B], ac-[node(+, [A, B])-Id1]].

test(ac_flattening, true(Id1 == Id2)) :-
    phrase(( add_term(a+(b+c), Id1),
             add_term((a+b)+c, Id2)
          ), [egraph-[], ac-[]], Out),
    Out =@= [egraph-[a-A, b-B, c-C], ac-[node(+, [A, B, C])-Id1]].

test(ac_shared_subterm) :-
    phrase(add_term(a+a, Id), [egraph-[], ac-[]], Out),
    Out =@= [egraph-[a-A], ac-[node(+, [A, A])-Id]].

:- end_tests(emt_add_ac).

:- begin_tests(emt_rebuild).

test(empty_graph) :-
    phrase(rebuild([]), [egraph-[], ac-[]], Out),
    Out == [egraph-[], ac-[]].

test(noop_no_congruence) :-
    phrase(rebuild([]), [egraph-[a-X, b-Y], ac-[]], Out),
    Out =@= [egraph-[a-X, b-Y], ac-[]].

test(duplicate_nodes_merge, true(X == Y)) :-
    phrase(rebuild([]), [egraph-[a-X, a-Y], ac-[]], Out),
    Out =@= [egraph-[a-X], ac-[]].

test(congruence_closure, true((X == Y, A == B))) :-
    phrase(rebuild([]), [egraph-[a-X, a-Y, f(X)-A, f(Y)-B], ac-[]], Out),
    Out =@= [egraph-[a-X, f(X)-A], ac-[]].

test(already_canonical) :-
    phrase(rebuild([]), [egraph-[a-X, f(X)-A], ac-[]], Out),
    Out =@= [egraph-[a-X, f(X)-A], ac-[]].

test(explicit_union_triggers_congruence, true((A == B, C == D))) :-
    phrase(rebuild([A=B]), [egraph-[a-A, b-B, g(A)-C, g(B)-D], ac-[]], Out),
    Out =@= [egraph-[a-A, b-A, g(A)-C], ac-[]].

test(ac_canonization, true(Id1 == Id2)) :-
    phrase(rebuild([]),
           [egraph-[], ac-[node(+,[B,A])-Id1, node(+,[A,B])-Id2]],
           Out),
    Out =@= [egraph-[], ac-[node(+,[A,B])-Id1]].

test(ac_congruence_from_union, true((A == B, Id1 == Id2))) :-
    phrase(rebuild([A=B]),
           [egraph-[a-A, b-B], ac-[node(+,[A,X])-Id1, node(+,[B,X])-Id2]],
           Out),
    Out =@= [egraph-[a-A, b-A], ac-[node(+,[A,X])-Id1]].

test(rebuild_fixpoint) :-
    phrase(rebuild([]), [egraph-[a-X, f(X)-A], ac-[node(+,[X])-N]], Out),
    Out =@= [egraph-[a-X, f(X)-A], ac-[node(+,[X])-N]].

:- end_tests(emt_rebuild).

:- begin_tests(emt_critical_pairs).

% Direct tests for critical_pairs//0, the DCG that enumerates the
% AC critical pairs of a rule set. Each rule is L-R with L a sorted
% (multi)set LHS and R a sorted RHS multiset; an output item C1-C2
% is the (canonized) pair of RHSes obtained by overlapping the two
% LHSes at their common peak.

test(empty) :-
    phrase(critical_pairs([]), Pairs),
    Pairs == [].

test(single_rule) :-
    A = a, B = b,
    phrase(critical_pairs([[A,B]-[B]]), Pairs),
    Pairs == [].

test(disjoint_lhs) :-
    A = a, B = b, X = x, Y = y, D = d,
    Rules = [[A,B]-[B], [X,Y]-[D]],
    phrase(critical_pairs(Rules), Pairs),
    Pairs == [].

% Rules {A,B}->B and {A,A}->C overlap on A, peak {A,A,B}.
%   apply {A,B}->B : peak \ {A,B} = {A}, ∪ {B} = {A,B}
%   apply {A,A}->C : peak \ {A,A} = {B}, ∪ {C} = {B,C}
% so the critical pair is [A,B]-[B,C].

test(overlap_two_rules, true(Pairs =@= [[A,B]-[B,C]])) :-
    A = a, B = b, C = c,
    Rules = [[A,B]-[B], [A,A]-[C]],
    phrase(critical_pairs(Rules), Pairs).

% §2.3 rule set fed straight to critical_pairs//0: three pairwise
% overlaps give two critical pairs ([A,B]-[B,C] and [B,C]-[A,D]).

test(two_three_rules, true(Pairs =@= [[A,B]-[B,C], [B,C]-[A,D]])) :-
    A = a, B = b, C = c, D = d,
    Rules = [[A,B]-[B], [A,A]-[C], [B,C]-[D]],
    phrase(critical_pairs(Rules), Pairs).

:- end_tests(emt_critical_pairs).

:- begin_tests(emt_ac_closure).

% Direct tests for ac_closure/3, the Buchberger-style AC-closure step
% that turns a set of AC-nodes (already canonized) into a list of
% new e-class merges. ac_closure/3 ignores its third argument; it is
% the discarded output theory-data slot supplied by with_theory//2.

test(empty) :-
    ac_closure(Unifs, [], _),
    Unifs == [].

test(single_node) :-
    A = a, B = b,
    ac_closure(Unifs, [node(+,[A,B])-B], _),
    Unifs == [].

test(disjoint_rules) :-
    A = a, B = b, C = c, D = d,
    Nodes = [node(+,[A,B])-B, node(+,[C,D])-D],
    ac_closure(Unifs, Nodes, _),
    Unifs == [].

% Thesis §2.3 fed directly to ac_closure/3: rules {A,B}->B, {A,A}->C,
% {B,C}->D. The {A,B}/{A,A} overlap peaks at {A,A,B} and yields the
% critical pair (B, D), i.e. the merge B=D.

test(two_three_overlap, true(Unifs =@= [B=D, D=B])) :-
    A = a, B = b, C = c, D = d,
    Nodes = [node(+,[A,B])-B, node(+,[A,A])-C, node(+,[B,C])-D],
    ac_closure(Unifs, Nodes, _).

:- end_tests(emt_ac_closure).

:- begin_tests(emt_ac_closure_23).

% Thesis §2.3 example. Three ground facts:
%   a+b = b,  a+a = c,  c+b = d
% imply  b = d  via the deduction
%   b = a+b = a+(a+b) = (a+a)+b = c+b = d
% The current rebuild//1 cannot see this: the AC-nodes {A,B}, {A,A},
% {B,C} are distinct multisets so congruence closure merges nothing.
% AC-closure (Buchberger) computes the overlap of {A,B} and {A,A}
% on {A}, peak {A,A,B}, critical pair (B, D) -> union B=D.

test(b_equals_d, true(B == D)) :-
    phrase(( add_term(a, _A), add_term(b, B),
             add_term(c, C), add_term(d, D),
             add_term(a+b, AB),
             rebuild([AB=B]),
             add_term(a+a, AA),
             rebuild([AA=C]),
             add_term(c+b, CB),
             rebuild([CB=D]) ),
           [egraph-[], ac-[]], _EGraph),
    B == D.

:- end_tests(emt_ac_closure_23).

:- begin_tests(emt_ac_closure_372).

% Thesis §3.7.2 example (endless overlap). Two ground facts:
%   a+b = d,  a+c = e
% The AC-rules {A,B}->D and {A,C}->E overlap on {A}, peak {A,B,C},
% giving the critical pair  {C,D} = {B,E}, i.e.  c+d = b+e.
% With the atomic-RHS (integrated) approach this does not terminate:
% each new rule spawns further unjoinable critical pairs.
% The general side-table stores {C,D} -> {B,E} (or reverse) and
% terminates. So this test needs the general side-table to pass.

test(cd_equals_be, true(CD == BE)) :-
    phrase(( add_term(a, _A), add_term(b, _B),
             add_term(c, _C), add_term(d, D),
             add_term(e, E),
             add_term(a+b, AB),
             rebuild([AB=D]),
             add_term(a+c, AC),
             rebuild([AC=E]),
             add_term(c+d, CD),
             add_term(b+e, BE),
             rebuild([]) ),
           [egraph-[], ac-[]], _S7),
    CD == BE.

:- end_tests(emt_ac_closure_372).
