import json
import pytest

from isabelle_parser import parse, ParsingError, reset_lexer, thy_lexer


@pytest.mark.parametrize("name,test_input, expected", [
    ('parse_theory', """
    theory Consensus
    imports RDR
    begin
    end
    """, True),
    ('parse_theory_docs', """
section \\<open>The Consensus Data Type\\<close>

theory Consensus
imports RDR
begin

text \\<open>This theory provides a model for the RDR locale, thus showing
  that the assumption of the RDR locale are consistent.\\<close>

end""",
     True),
    ('parse_theory_typedecl', """
theory Consensus
imports RDR
begin

typedecl proc
typedecl val

end
""",
     True),
    ('parse_theory_locale', """
theory Consensus
imports RDR
begin

locale Consensus
\\<comment> \\<open>To avoid name clashes\\<close>
begin
end
end""",
     True),
    ('parse_theory_fun', """
theory Consensus
imports RDR
begin

fun \\<delta>::"val option \\<Rightarrow> (proc \\<times> val) \\<Rightarrow> val option" (infix "\\<bullet>" 65) where
  "\\<delta> None r = Some (snd r)"
| "\\<delta> (Some v) r = Some v"

end""",
     True),
    ('parse_theory_interpretation', """
theory Consensus
imports RDR
begin

interpretation pre_RDR \\<delta> \\<gamma> None .

end""", True),
    ('parse_theory_notation', """
theory Consensus
imports RDR
begin

notation exec (infix "\\<star>" 65)
notation less_eq (infix "\\<preceq>" 50 )
notation None ("\\<bottom>")

end""",
     True),
    ('parse_theory_lemma_fixes', """
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
     True),
    ('parse_theory_lemma_obtain', """
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
     True),
    ('parse_theory_lemma_obtains', """
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
     True),
])
def test_parse(name, test_input, expected):
    source_code = test_input.strip()
    try:
        reset_lexer(thy_lexer)
        ast = parse(source_code)
        print(json.dumps(ast, indent=2))
        assert expected, f"{name}: Expected {expected}, got True"
        assert ast is not None, f"{name}: Expected AST, got None"
    except ParsingError as e:
        print(e.with_source_code(source_code))
        assert not expected, f"{name}: Expected {expected}, got False"

