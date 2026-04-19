import pytest

from isabelle_parser import ParsingError, parse


@pytest.mark.parametrize(
    "name,test_input,expected",
    [
        # -----------------------------------------------------------------------
        # Original cases
        # -----------------------------------------------------------------------
        (
            "parse_theory",
            """
    theory Consensus
    imports RDR
    begin
    end
    """,
            True,
        ),
        (
            "parse_theory_docs",
            """
section \\<open>The Consensus Data Type\\<close>

theory Consensus
imports RDR
begin

text \\<open>This theory provides a model for the RDR locale, thus showing
  that the assumption of the RDR locale are consistent.\\<close>

end""",
            True,
        ),
        (
            "parse_theory_typedecl",
            """
theory Consensus
imports RDR
begin

typedecl proc
typedecl val

end
""",
            True,
        ),
        (
            "parse_theory_locale",
            """
theory Consensus
imports RDR
begin

locale Consensus
\\<comment> \\<open>To avoid name clashes\\<close>
begin
end
end""",
            True,
        ),
        (
            "parse_theory_fun",
            """
theory Consensus
imports RDR
begin

fun \\<delta>::"val option \\<Rightarrow> (proc \\<times> val) \\<Rightarrow> val option" (infix "\\<bullet>" 65) where
  "\\<delta> None r = Some (snd r)"
| "\\<delta> (Some v) r = Some v"

end""",
            True,
        ),
        (
            "parse_theory_interpretation",
            """
theory Consensus
imports RDR
begin

interpretation pre_RDR \\<delta> \\<gamma> None .

end""",
            True,
        ),
        (
            "parse_theory_notation",
            """
theory Consensus
imports RDR
begin

notation exec (infix "\\<star>" 65)
notation less_eq (infix "\\<preceq>" 50 )
notation None ("\\<bottom>")

end""",
            True,
        ),
        (
            "parse_theory_lemma_fixes",
            """
theory Consensus
imports RDR
begin

lemma single_use:
  fixes r rs
  shows  "\\<bottom> \\<star> ([r]@rs) = Some (snd r)"
proof (induct rs)
  case Nil
  thus ?case by simp
next
  case (Cons r rs)
  thus ?case by auto
qed

end""",
            True,
        ),
        (
            "parse_theory_lemma_obtain",
            """
theory Consensus
imports RDR
begin

lemma bot: "\\<exists> rs . s = \\<bottom> \\<star> rs"
proof (cases s)
  case None
  hence "s = \\<bottom> \\<star> []" by auto
  thus ?thesis by blast
next
  case (Some v)
  obtain r where "\\<bottom> \\<star> [r] = Some v" by force
  thus ?thesis using Some by metis
qed
 end""",
            True,
        ),
        (
            "parse_theory_lemma_obtains",
            """
theory Consensus
imports RDR
begin

lemma prec_eq_None_or_equal:
fixes s1 s2
assumes "s1 \\<<preceq> s2"
shows "s1 = None \\<<or> s1 = s2" using assms single_use
proof -
  { assume 1:"s1 \\<<noteq> None" and 2:"s1 \\<noteq> s2"
    obtain r rs where 3:"s1 = \\<bottom> \\<<star> ([r]@rs)" using bot using 1
      by (metis append_butlast_last_id pre_RDR.exec.simps(1))
    obtain rs' where 4:"s2 = s1 \\<star> rs'" using assms
      by (auto simp add:less_eq_def)
    have "s2 = \\<bottom> \\<star> ([r]@(rs@rs'))" using 3 4
      by (metis exec_append)
    hence "s1 = s2" using 3
      by (metis single_use)
    with 2 have False by auto }
  thus ?thesis by blast
qed
end""",
            True,
        ),
        (
            "parse_theory_nested_comments",
            """
theory NestedComments
     imports Main
begin
\\<comment> \\<open> some text \\<open> inner text \\<close> final text \\<close>
end""",
            True,
        ),

        # -----------------------------------------------------------------------
        # Theory header variants
        # -----------------------------------------------------------------------
        (
            "theory_header_multiple_imports",
            "theory T imports Main HOL.List Complex_Main begin end",
            True,
        ),
        (
            "theory_header_qualified_name",
            "theory A.B imports Main begin end",
            True,
        ),
        (
            "theory_header_keywords_clause",
            'theory T imports Main keywords "mycommand" :: thy_decl begin end',
            True,
        ),
        (
            "theory_header_empty_body",
            "theory T imports Main begin end",
            True,
        ),

        # -----------------------------------------------------------------------
        # Documentation blocks
        # -----------------------------------------------------------------------
        (
            "doc_text_quoted_string",
            'theory T imports Main begin\ntext "quoted string documentation"\nend',
            True,
        ),
        (
            "doc_subsection",
            "theory T imports Main begin\nsubsection \\<open>A subsection\\<close>\nend",
            True,
        ),
        (
            "doc_subsubsection",
            "theory T imports Main begin\nsubsubsection \\<open>A subsubsection\\<close>\nend",
            True,
        ),
        (
            "doc_chapter",
            "theory T imports Main begin\nchapter \\<open>A chapter\\<close>\nend",
            True,
        ),
        (
            "doc_txt",
            "theory T imports Main begin\ntxt \\<open>Informal text\\<close>\nend",
            True,
        ),
        (
            "doc_paragraph",
            "theory T imports Main begin\nparagraph \\<open>A paragraph\\<close>\nend",
            True,
        ),
        (
            "doc_cartouche_in_definition",
            "theory T imports Main begin\ndefinition mydef :: \"nat\" where \\<open>mydef = 0\\<close>\nend",
            True,
        ),
        (
            "doc_nested_cartouche_in_body",
            "theory T imports Main begin\ntext \\<open>outer \\<open>inner\\<close> outer\\<close>\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Type declarations
        # -----------------------------------------------------------------------
        (
            "typedecl_with_type_param",
            "theory T imports Main begin\ntypedecl 'a mytype\nend",
            True,
        ),
        (
            "type_synonym_simple",
            'theory T imports Main begin\ntype_synonym mynat = "nat"\nend',
            True,
        ),
        (
            "type_synonym_parameterised",
            "theory T imports Main begin\ntype_synonym 'a mylist = \"'a list\"\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Constant declarations
        # -----------------------------------------------------------------------
        (
            "consts_single",
            'theory T imports Main begin\nconsts myconst :: "nat"\nend',
            True,
        ),
        (
            "consts_multiple",
            'theory T imports Main begin\nconsts\n  foo :: "nat"\n  bar :: "bool"\nend',
            True,
        ),
        (
            "consts_with_mixfix",
            'theory T imports Main begin\nconsts myop :: "nat \\<Rightarrow> nat" ("op _" 50)\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Definition & abbreviation
        # -----------------------------------------------------------------------
        (
            "definition_simple",
            'theory T imports Main begin\ndefinition mydef :: "nat" where "mydef = 0"\nend',
            True,
        ),
        (
            "definition_function_type",
            'theory T imports Main begin\ndefinition myfun :: "nat \\<Rightarrow> nat" where "myfun n = n + 1"\nend',
            True,
        ),
        (
            "abbreviation",
            'theory T imports Main begin\nabbreviation myabbrev :: "bool" where "myabbrev \\<equiv> True"\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Goals (lemma/theorem/corollary/proposition)
        # -----------------------------------------------------------------------
        (
            "lemma_sorry",
            'theory T imports Main begin\nlemma foo: "True" sorry\nend',
            True,
        ),
        (
            "lemma_oops",
            'theory T imports Main begin\nlemma foo: "False" oops\nend',
            True,
        ),
        (
            "theorem_sorry",
            'theory T imports Main begin\ntheorem myThm: "1 + 1 = 2" sorry\nend',
            True,
        ),
        (
            "corollary_sorry",
            'theory T imports Main begin\ncorollary myCorol: "True" sorry\nend',
            True,
        ),
        (
            "proposition_sorry",
            'theory T imports Main begin\nproposition myProp: "True" sorry\nend',
            True,
        ),
        (
            "lemma_by_simp",
            'theory T imports Main begin\nlemma "1 = 1" by simp\nend',
            True,
        ),
        (
            "lemma_by_auto",
            'theory T imports Main begin\nlemma foo: "True" by auto\nend',
            True,
        ),
        (
            "lemma_in_locale",
            'theory T imports Main begin\nlemma (in my_locale) foo: "True" by simp\nend',
            True,
        ),
        (
            "lemma_shows_clause",
            'theory T imports Main begin\nlemma foo\n  shows "True"\n  by simp\nend',
            True,
        ),
        (
            "lemma_assumes_shows",
            'theory T imports Main begin\nlemma foo:\n  assumes "P"\n  shows "P"\n  using assms by simp\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Proof tactics
        # -----------------------------------------------------------------------
        (
            "proof_apply_done",
            'theory T imports Main begin\nlemma "True"\n  apply simp\n  done\nend',
            True,
        ),
        (
            "proof_apply_sequence",
            'theory T imports Main begin\nlemma "True \\<and> True"\n  apply (rule conjI)\n  apply simp\n  apply simp\n  done\nend',
            True,
        ),
        (
            "proof_by_two_methods",
            'theory T imports Main begin\nlemma "True" by (rule TrueI) simp\nend',
            True,
        ),
        (
            "proof_qed",
            'theory T imports Main begin\nlemma "True"\nproof\n  show "True" by simp\nqed\nend',
            True,
        ),
        (
            "proof_assume_show",
            'theory T imports Main begin\nlemma\n  assumes H: "P"\n  shows "P"\nproof -\n  show "P" using H .\nqed\nend',
            True,
        ),
        (
            "proof_next",
            'theory T imports Main begin\nlemma "True \\<and> True"\nproof\n  show "True" by simp\nnext\n  show "True" by simp\nqed\nend',
            True,
        ),
        (
            "proof_curly_brace_block",
            'theory T imports Main begin\nlemma prec_eq:\n  fixes s1 s2\n  shows "True"\nproof -\n  { assume 1:"True"\n    have "True" by simp }\n  thus ?thesis by blast\nqed\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Inductive / coinductive
        # -----------------------------------------------------------------------
        (
            "inductive",
            'theory T imports Main begin\ninductive even :: "nat \\<Rightarrow> bool" where\n  "even 0"\n| "even n \\<Longrightarrow> even (Suc (Suc n))"\nend',
            True,
        ),
        (
            "coinductive",
            'theory T imports Main begin\ncoinductive inf_stream :: "nat \\<Rightarrow> bool" where\n  "inf_stream n"\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Datatype
        # -----------------------------------------------------------------------
        (
            "datatype_parameterised",
            "theory T imports Main begin\ndatatype 'a tree = Leaf | Node \"'a tree\" 'a \"'a tree\"\nend",
            True,
        ),
        (
            "datatype_simple_enum",
            "theory T imports Main begin\ndatatype mybool = MyTrue | MyFalse\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Locale structural variants
        # -----------------------------------------------------------------------
        (
            "locale_bare",
            "theory T imports Main begin\nlocale my_locale\nend",
            True,
        ),
        (
            "locale_with_fixes",
            'theory T imports Main begin\nlocale my_locale = fixes f :: "nat \\<Rightarrow> nat"\nend',
            True,
        ),
        (
            "locale_with_assumes",
            'theory T imports Main begin\nlocale my_locale = fixes f :: "nat \\<Rightarrow> nat"\n  assumes mono: "f x \\<le> f y"\nend',
            True,
        ),
        (
            "locale_with_lemma",
            'theory T imports Main begin\nlocale my_locale = fixes f :: "nat \\<Rightarrow> nat"\nbegin\nlemma "True" by simp\nend\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Sublocale
        # -----------------------------------------------------------------------
        (
            "sublocale",
            "theory T imports Main begin\nsublocale A < B by simp\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Notation
        # -----------------------------------------------------------------------
        (
            "no_notation",
            'theory T imports Main begin\nno_notation myop ("_ \\<oplus> _" [70,71] 70)\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # ML / setup
        # -----------------------------------------------------------------------
        (
            "ml",
            "theory T imports Main begin\nml \\<open>val x = 1\\<close>\nend",
            True,
        ),
        (
            "setup",
            "theory T imports Main begin\nsetup \\<open>fn _ => ()\\<close>\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Axiomatization
        # -----------------------------------------------------------------------
        (
            "axiomatization_empty",
            "theory T imports Main begin\naxiomatization\nend",
            True,
        ),
        (
            "axiomatization_with_where",
            'theory T imports Main begin\naxiomatization\n  myax :: "nat"\n  where ax1: "myax > 0"\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Context blocks
        # -----------------------------------------------------------------------
        (
            "context_anonymous",
            'theory T imports Main begin\ncontext begin\nlemma "True" by simp\nend\nend',
            True,
        ),
        (
            "context_named",
            'theory T imports Main begin\ncontext my_locale begin\nlemma "True" by simp\nend\nend',
            True,
        ),

        # -----------------------------------------------------------------------
        # Hide declarations
        # -----------------------------------------------------------------------
        (
            "hide_const",
            "theory T imports Main begin\nhide_const (open) myconst\nend",
            True,
        ),
        (
            "hide_type",
            "theory T imports Main begin\nhide_type mytype\nend",
            True,
        ),
        (
            "hide_fact",
            "theory T imports Main begin\nhide_fact myfact\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Declare & lemmas
        # -----------------------------------------------------------------------
        (
            "declare",
            "theory T imports Main begin\ndeclare simp_thms [simp]\nend",
            True,
        ),
        (
            "lemmas",
            "theory T imports Main begin\nlemmas my_lemmas = conjI disjI1\nend",
            True,
        ),

        # -----------------------------------------------------------------------
        # Edge cases
        # -----------------------------------------------------------------------
        (
            "outer_comment_ignored",
            "theory T imports Main begin\n(* outer comment *)\nlemma \"True\" by simp\nend",
            True,
        ),
        (
            "long_import_list",
            "theory T imports " + " ".join(f"Lib{i}" for i in range(10)) + " begin end",
            True,
        ),
        (
            "multiple_lemmas",
            "theory T imports Main begin\n"
            'lemma a: "True" by simp\n'
            'lemma b: "True \\<and> True" by simp\n'
            'lemma c: "1 = (1::nat)" by simp\n'
            "end",
            True,
        ),
    ],
)
def test_parse(name, test_input, expected):
    source_code = test_input.strip()
    try:
        ast = parse(source_code)
        if ast:
            print(ast.pretty())
        else:
            print("Parsing failed.")
        assert expected, f"{name}: Expected {expected}, got True"
        assert ast is not None, f"{name}: Expected AST, got None"
    except ParsingError as e:
        print(e.with_source_code(source_code))
        assert not expected, f"{name}: Expected {expected}, got False"
