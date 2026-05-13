:- module(bottom_up_parsing, [parse/2]).
:- use_module(clpegraph).

% 1. Lexicon Rules
egraph:rewrite(lex_i, i, np(i)).
egraph:rewrite(lex_saw, saw, v(saw)).
egraph:rewrite(lex_the, the, det(the)).
egraph:rewrite(lex_man, man, n(man)).
egraph:rewrite(lex_with, with, p(with)).
egraph:rewrite(lex_tel, telescope, n(telescope)).

% 2. Grammar Rules
egraph:rewrite(s_np_vp, np(A)-vp(B), s(np(A), vp(B))).
egraph:rewrite(np_det_n, det(A)-n(B), np(det(A), n(B))).
egraph:rewrite(np_np_pp, np(A)-pp(B), np(np(A), pp(B))).
egraph:rewrite(vp_v_np, v(A)-np(B), vp(v(A), np(B))).
egraph:rewrite(vp_vp_pp, vp(A)-pp(B), vp(vp(A), pp(B))).
egraph:rewrite(pp_p_np, p(A)-np(B), pp(p(A), np(B))).

% 3. Structural Rules
egraph:rewrite(seq_assoc_l, A-(B-C), (A-B)-C).
egraph:rewrite(seq_assoc_r, (A-B)-C, A-(B-C)).

grammar_rules([
   lex_i, lex_saw, lex_the, lex_man, lex_with, lex_tel,
   s_np_vp, np_det_n, np_np_pp, vp_v_np, vp_vp_pp, pp_p_np,
   seq_assoc_l, seq_assoc_r
]).

parse(Input, Parse) :-
   Input #= i-(saw-(the-(man-(with-(the-telescope))))),
   grammar_rules(Rules),
   saturate(Rules),
   Input ?#= s(_, _),
   true.
