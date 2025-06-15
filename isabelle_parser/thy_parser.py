import logging
import os
from typing import Any, List

from lark import Lark, Transformer, Tree
from lark.tree import Meta

logger = logging.getLogger(__name__)


def load_parser(start: str="start") -> Lark:
    # Construct the path to the .lark file
    grammar_path = os.path.join(os.path.dirname(__file__), "thy_grammar.lark")

    # Load the grammar file and create a Lark parser
    with open(grammar_path) as grammar_file:
        parser = Lark(
            grammar_file, start=start, parser="earley", propagate_positions=True
        )

    return parser


def parse(input_text: str, parser: Lark | None=None) -> Any | None:
    if parser is None:
        parser = load_parser()
    tree = parser.parse(input_text)
    transformer = PositionPrinter()
    return transformer.transform(tree)


class PositionPrinter(Transformer):
    def name(self, items: Any) -> Tree:
        concatenated = concatenate(items)
        return with_position(Tree("name", [concatenated], Meta()), *get_position(items))

    def embedded(self, items: Any) -> Tree:
        concatenated = concatenate(items)
        return with_position(
            Tree("embedded", [concatenated], Meta()), *get_position(items)
        )

    def letter(self, items: Any) -> Tree:
        token = items[0]
        if hasattr(token, "value"):
            value = token.value
        else:
            value = "".join(str(item) for item in items)
        return with_position(Tree("letter", [value], Meta()), *get_position(items))

def with_position(tree: Tree, line: int | None, column: int | None) -> Tree:
    if line is not None and column is not None:
        if not hasattr(tree.meta, "line") or not tree.meta.line:
            tree.meta.line = line
            tree.meta.column = column
    return tree


def get_position(items: List[Any]) -> tuple[int | None, int | None]:
    if items and len(items) > 0:
        token = items[0]
        line = column = None
        if hasattr(token, "line"):
            line = token.line
            column = token.column
        elif hasattr(token, "meta"):  # Tree with meta
            line = token.meta.line
            column = token.meta.column
        elif isinstance(token, dict) and "line" in token and "column" in token:
            line = token["line"]
            column = token["column"]
        return (line, column)
    return (None, None)


def concatenate(items: List[Any]) -> str:
    concatenated = ""
    for item in items:
        if hasattr(item, "value"):
            concatenated += item.value
        elif isinstance(item, dict) and "value" in item:
            concatenated += item["value"]
        elif isinstance(item, str):
            concatenated += item
        elif isinstance(item, Tree):
            concatenated += "".join(str(child) for child in item.children)
        else:
            concatenated += str(item)
    return concatenated
