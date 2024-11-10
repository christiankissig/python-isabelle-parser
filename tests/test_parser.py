import json
import pytest

from isabelle_parser import parse, ParsingError, reset_lexer, thy_lexer


@pytest.mark.parametrize( "name,test_input, expected", [
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

end""", True),
('parse_theory_typedecl', """
theory Consensus
imports RDR
begin

typedecl proc
typedecl val

end
""", True),
('parse_theory_locale', """
theory Consensus
imports RDR
begin

locale Consensus
\\<comment> \\<open>To avoid name clashes\\<close>
begin
end
end""", True),
('parse_theory_fun', """
theory Consensus
imports RDR
begin

fun \\<delta>::"val option \\<Rightarrow> (proc \\<times> val) \\<Rightarrow> val option" (infix "\\<bullet>" 65) where
  "\\<delta> None r = Some (snd r)"
| "\\<delta> (Some v) r = Some v"

end
""", True),
('parse_theory_interpretation', """
theory Consensus
imports RDR
begin

interpretation pre_RDR \\<delta> \\<gamma> None .

end
""", True),
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

