import re


def test_re():
    input = "not_irreducible\\<^sub>d_lead_coeff_factors"
    pattern = re.compile(r'[a-zA-Z_][a-zA-Z_0-9\']*(\\<\^sub>[a-zA-Z0-9_]*)?')
    assert pattern.fullmatch(input)
