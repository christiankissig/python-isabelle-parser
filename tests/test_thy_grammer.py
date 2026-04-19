import pytest
from lark import ParseError
from isabelle_parser import parse, load_parser


class GrammerTester:
    parsers = {}

    def matches_rule(self, rule_name: str | None, text: str) -> bool:
        if rule_name is None:
            raise ValueError("Rule name must not be None")
        if rule_name not in self.parsers:
            parser = load_parser(rule_name)
            if parser is None:
                raise ValueError(f"Parser for rule '{rule_name}' could not be loaded")
            self.parsers[rule_name] = parser
        try:
            parse(text, self.parsers[rule_name])
            return True
        except ParseError:
            return False


grammer_tester = GrammerTester()

thy = """
obtain p where "((p::name prm) \\<bullet> (xvec::name list)) \\<sharp>* T" and "(p \\<bullet> xvec) \\<sharp>* xvec"
                and S: "(set p) \\<subseteq> set xvec \\<times> set (p \\<bullet> xvec)"
                and "distinctPerm p"
       by(rule_tac xvec=xvec and c="(T, xvec)" in name_list_avoiding) auto

     from \\<open>length xvec = length Tvec\\<close> have "length(p \\<bullet> xvec) = length Tvec" by simp
     moreover from \\<open>(p \\<bullet> xvec) \\<sharp>* T\\<close> have "(p \\<bullet> p \\<bullet> xvec) \\<sharp>* (p \\<bullet>
        T)"
       by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
"""

# ---------------------------------------------------------------------------
# Sub-rule grammar tests
# (test_string, rule_name, should_match)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("test_string,rule_name,should_match", [
    # --- name rule ---
    (r"lpfp\<^sub>c",   "name", True),
    (r"\<gamma>_fun",   "name", True),
    ("def_ts",          "name", True),
    ("my_lemma'",       "name", True),
    ("x1",              "name", True),
    ("HOL.List",        "name", True),
    # --- proof_state rule ---
    (thy,                                                          "proof_state", True),
    # obtain regression: proof_state must include proof_prove on obtain
    (r'obtain r where "P r" by force',                            "proof_state", True),
    ('obtain p where "P x" by(rule_tac x=p in myThm)',            "proof_state", True),
    ('obtain p where "P x" by(rule_tac x=p and y=q in myThm)',    "proof_state", True),
    ('obtain p where "P x" by(rule_tac x=p in myThm) auto',       "proof_state", True),
], ids=[
    "name_subscript",
    "name_greek_prefix",
    "name_underscore",
    "name_prime",
    "name_numeric_suffix",
    "name_qualified",
    "proof_state_afp_snippet",
    "proof_state_obtain_by_force",
    "proof_state_obtain_by_paren_single",
    "proof_state_obtain_by_paren_and",
    "proof_state_obtain_by_paren_auto",
])
def test_grammar_rules(test_string, rule_name, should_match):
    result = grammer_tester.matches_rule(rule_name, test_string)
    assert result == should_match, (
        f"Expected '{test_string}' to "
        f"{'match' if should_match else 'not match'} rule '{rule_name}'"
    )
