from lark import Lark

import logging
import os


logger = logging.getLogger(__name__)


def _load_parser():
    # Construct the path to the .lark file
    grammar_path = os.path.join(os.path.dirname(__file__), 'thy_grammar.lark')

    # Load the grammar file and create a Lark parser
    with open(grammar_path) as grammar_file:
        parser = Lark(grammar_file, start='start', parser='earley')

    return parser


def parse(input_text):
    parser = _load_parser()
    try:
        tree = parser.parse(input_text)
        return tree
    except Exception as e:
        print(f"Error parsing input: {e}")
