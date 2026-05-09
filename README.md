# Prolog E-Graph

An SWI-Prolog implementation of an E-graph (Equivalence Graph) data structure for term rewriting, congruence closure, and e-matching. 

E-graphs represent equivalence classes of expressions, allowing rewrite rules to be applied non-destructively before extracting representations based on cost.

## Dependencies

This package relies on the following SWI-Prolog standard libraries:
* `library(dcg/high_order)`
* `library(ordsets)`
* `library(rbtrees)`
* `library(heaps)`

## Installation

This package requires SWI-Prolog version 9.3.23 or later.

To install as a pack (if published) or run locally:
```prolog
?- pack_install(egraph).
```

## Defining Rewrite Rules

Rules are defined via the `egraph:rewrite` multifile predicate. During compilation, these rules generate the underlying DCG predicates that manipulate the E-graph.

### Rule Syntax Forms
* `egraph:rewrite(Name, Lhs, Rhs)`
* `egraph:rewrite(Name, Lhs, Rhs, RhsOptions)`
* `egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions)`
* `egraph:rewrite(Name, Lhs, LhsOptions, Rhs, RhsOptions) :- Body`
* `egraph:analyze(Name, Lhs, RhsOptions)`
* `egraph:analyze(Name, Lhs, LhsOptions, RhsOptions)`
* `egraph:analyze(Name, Lhs, LhsOptions, RhsOptions) :- Body`
* `egraph:merge_property(Name, V1, V2, Merged)`
* `egraph:merge_property(Name, V1, V2, Merged) :- Body`
* `egraph:rule(Name, LhsPatterns, RhsPatterns)`
* `egraph:rule(Name, LhsPatterns, RhsPatterns) :- Body`
* `egraph:rule(Name, LhsPatterns, RhsPatterns, RhsOptions)`
* `egraph:rule(Name, LhsPatterns, RhsPatterns, RhsOptions) :- Body`
* `egraph:rule(Name, LhsPatterns, LhsOptions, RhsPatterns, RhsOptions)`
* `egraph:rule(Name, LhsPatterns, LhsOptions, RhsPatterns, RhsOptions) :- Body`

**Note on Signatures:**
* For `egraph:rewrite` and `egraph:analyze`, `Lhs` and `Rhs` are single structural terms.
* For `egraph:rule`, `LhsPatterns` and `RhsPatterns` must be a list of `Pattern-Id` pairs (e.g., `[f(A)-Id1, g(B)-Id2]`). Shared class Ids between left and right patterns are automatically unified.
* `Options` (both Lhs and Rhs) are a list of property compounds in the form `Name(Key, Value)`. For `egraph:rewrite` and `egraph:analyze` rules, a shorthand `Name(Value)` can be used, which implicitly uses the pattern's class Id as the `Key`.
  * Lhs options will "get" the property and can be prefixed by `\+` to negate the lookup.
  * Rhs options will "set" the property.
  * `cost(Cost)` is a special option that sets the structural cost of the node.

### Examples

```prolog
:- use_module(library(egraph)).

% Algebraic rules
egraph:rewrite(comm_add, A+B, B+A).
egraph:rewrite(assoc_add, A+(B+C), (A+B)+C).

% Rules with custom cost
egraph:rewrite(factorize_aa, A+A, 2*A, [cost(9r10)]).

% Rules with left-hand side conditions
egraph:rewrite(reduce_add0, A+B, [const(B, 0)], A, []).

% Rules with a Prolog body
egraph:rewrite(constant_folding, A+B, [const(A, VA), const(B, VB)], VC, [const(VC)]) :-
   VC is VA + VB.

% Node Analysis (e.g., constant detection)
egraph:analyze(is_const, '$NODE'(A), [const(A)]) :-
   number(A).

% Property merging when e-classes are unioned
egraph:merge_property(const, V1, V2, Merged) :-
   (  V1 =:= V2
   -> Merged = V1
   ;  domain_error(V1, V2)
   ).

% Dict support
egraph:rewrite(operator_fusion, array{op: array{op: A+B}+C}, array{op: A+B+C}).
```

## Usage

The interface uses Prolog's DCGs to thread the E-graph state. The E-graph itself is represented as a sorted list of pairs with the specific shape `Node-node(Id, Cost)`:
* `Node`: The structural term, literal value, or variable representation (e.g., `A+B`, `1`, `'$NODE'(X)`).
* `Id`: The equivalence class identifier (typically a Prolog variable).
* `Cost`: The structural cost of this specific node.

### Core Predicates

* **`add_term(+Term, -Id)//`** 
  Recursively adds a term (and its subterms) to the E-graph, unifying `Id` with its equivalence class.
* **`union(+Id1, +Id2)//`** 
  Merges two equivalence classes by their IDs.
* **`saturate(+Rules)//`** / **`saturate(+Rules, +MaxIterations)//`** 
  Applies a list of compiled rewrite rule names iteratively until the E-graph is saturated or the iteration limit is reached.
* **`extract(+Id, -Extracted)//`** 
  Extracts the optimal term from the E-graph based on term costs.
* **`extract_all(+Id, -Extracted)//`** 
  Extracts all optimal terms from the E-graph based on term costs.
* **`lookup(+Pair, +SortedPairs)`**
  Retrieves an e-class node from a sorted list of E-graph nodes.

### Example Workflow

```prolog
?- use_module(library(egraph)).
true.

?- phrase((
       add_term(a+0, Id),
       saturate([is_const, reduce_add0]),
       extract(Id, Optimized)
   ), [], _Graph).
Optimized = a,
...
```
