import json

from isabelle_parser import parse, ParsingError, reset_lexer, thy_lexer


def test_parse_theory():
    input = """
theory test_theory
imports
    Main
begin
end
    """
    ast = parse(input)
    assert ast is not None


def test_parse_lemma():
    input = """
    theory test_theory
    imports
        Main
    begin
        lemma some_lemma:
        assumes 1: "P"
        and 2: "Q"
        shows "R"
        apply simp
        by (clarsimp simp add: test.case(5))
    end
    """
    ast = parse(input.strip())
    # print(ast)
    assert ast is not None


def test_parse_I7_lemma():
    input = """
theory test_theory
imports
    Main
begin
lemma I7_preserves_pre_block_global_pre:
assumes 1: "block_cond t' ta ms \\<sigma>"
  and 2: "book_keeping \\<sigma> l t t'"
  and 3: "book_keeping \\<sigma> l t' ta"
  and 4: "preCond (history ms t) ms t"
  and 5: "preCond (history ms t') ms t'"
  and 6: "preCond (history ms ta) ms ta"
  and 7: "(history ms t, futures ms t) \\<in> futures_with_history"
  and 8: "(history ms t', futures ms t') \\<in> futures_with_history"
  and 9: "(history ms ta, futures ms ta) \\<in> futures_with_history"
  and 10: "rel \\<in> futures ms t"
  and 11: "minimal p rel"
  and 12: "fst p = I7"
  and 13: "prog ms ps \\<sigma> (fst p) (snd p) t ms' ps' \\<sigma>'"
  and 14: "full_inv ms ps \\<sigma>"
shows "block_cond t' ta ms' \\<sigma>'"
  apply (case_tac "t' = t")
  subgoal "t' = t"
    using assms(7) assms(10-13)
    apply narrow_top_level_futures
    using assms(1-6) assms(8) assms(13)
    by clarsimp+

  subgoal "t \\<neq> t'"
    using assms(7) assms(10-13)
    apply narrow_top_level_futures

    subgoal ""
      using assms(1-6) assms(8) assms(13)
      apply -
      apply (clarsimp simp add: futures_with_history_def)

      apply (elim conjE disjE)
      apply (simp_all add: prog_def abbr)
      apply (simp_all add: set_new_future_def less_eq_PC Let_def futures_by_history_def)
      apply (simp_all add: block_cond_def pre_block_def post_block_def)
      apply (simp_all add: post_block_def abbr preCond_def preconds)
      apply (simp_all add: Rcap_def Wcap_def full_inv_def)

    subgoal ""
        using assms(9)
        apply -
        apply (clarsimp simp add: futures_with_history_def)
        apply (elim conjE disjE; clarsimp)

        subgoal "" by (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse list.discI wfs_2_to_wfs)

end
    """
    source_code = input.strip()
    try:
        reset_lexer(thy_lexer)
        ast = parse(source_code)
        print(json.dumps(ast, indent=2))
        assert ast is not None
    except ParsingError as e:
        print(e.with_source_code(source_code))
        assert False


def test_parse_error():
    input = """
(*File: Lattice.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory Lattice imports Main begin
section\\<open>Lattices\\<close>

text\\<open>In preparation of the encoding of the type system of Hunt and
Sands, we define some abstract type of lattices, together with the
operations $\\bot$, $\\sqsubseteq$ and $\\sqcup$, and some obvious
axioms.\\<close>

typedecl L (*The lattice*)
    """
    source_code = input.strip()
    try:
        reset_lexer(thy_lexer)
        ast = parse(source_code)
        print(json.dumps(ast, indent=2))
        assert False
    except ParsingError as e:
        print(e.with_source_code(source_code))
        assert True
