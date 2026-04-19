"""
Unit tests for the thy_parser module API and rejection of invalid inputs.

Scope
-----
- Parser module API: load_parser() and parse() behaviour as Python objects.
- Rejection cases: inputs that must raise an exception rather than succeed.
  These cannot live in test_parser.py because that file's test_parse()
  catches only the project's ParsingError wrapper, while the underlying
  Lark parser raises lark.exceptions.UnexpectedEOF / UnexpectedCharacters
  directly for structurally invalid inputs.

Grammar coverage for valid inputs lives in test_parser.py and
test_thy_grammer.py.
"""

import pytest
from lark import Lark, Tree

from isabelle_parser import load_parser
from isabelle_parser.thy_parser import parse as _raw_parse


class TestParserInternals:
    def test_load_parser_returns_lark_instance(self):
        assert isinstance(load_parser("start"), Lark)

    def test_load_parser_with_subrule(self):
        assert isinstance(load_parser("proof_state"), Lark)

    def test_parse_returns_tree(self):
        p = load_parser("start")
        result = _raw_parse("theory T imports Main begin end", p)
        assert isinstance(result, Tree)

    def test_parse_with_explicit_parser(self):
        p = load_parser("start")
        result = _raw_parse("theory T imports Main begin end", p)
        assert result is not None

    def test_parse_with_none_uses_default_parser(self):
        result = _raw_parse("theory T imports Main begin end", None)
        assert result is not None


@pytest.mark.parametrize(
    "src",
    [
        "theory T imports Main end",  # missing begin
        "theory T imports Main begin",  # missing end
        "theory T begin end",  # missing imports
        "",  # empty string
        "THIS IS NOT VALID ISABELLE",  # garbage
    ],
    ids=[
        "missing_begin",
        "missing_end",
        "missing_imports",
        "empty_string",
        "garbage",
    ],
)
def test_invalid_input_raises(src):
    """Invalid theory inputs must raise rather than return a result."""
    with pytest.raises(Exception):
        _raw_parse(src, None)
