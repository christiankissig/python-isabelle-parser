from lark import Lark, Transformer, Tree, Token, v_args

import logging
import os


logger = logging.getLogger(__name__)


def _load_parser():
    # Construct the path to the .lark file
    grammar_path = os.path.join(os.path.dirname(__file__), 'thy_grammar.lark')

    # Load the grammar file and create a Lark parser
    with open(grammar_path) as grammar_file:
        parser = Lark(grammar_file,
                      start='start',
                      parser='earley',
                      propagate_positions=True)

    return parser


def parse(input_text):
    parser = _load_parser()
    try:
        tree = parser.parse(input_text)
        transformer = PositionPrinter()
        return transformer.transform(tree)
    except Exception as e:
        print(f"Error parsing input: {e}")


class PositionPrinter(Transformer):

    def name(self, items):
        concatenated = ''
        for item in items:
            if hasattr(item, 'value'):
                concatenated += item.value
            elif 'value' in item:
                concatenated += item['value']
            elif isinstance(item, str):
                concatenated += item
            else:
                concatenated += str(item)

        if items and len(items) > 0:
            return with_position('name', concatenated, items[0])
        else:
            return concatenated

    def letter(self, items):
        if items and len(items) > 0:
            token = items[0]
            if hasattr(token, 'value'):
                letter_value = token.value
                return with_position('letter', letter_value, token)

        return ''.join(str(item) for item in items)


def with_position(rule, value, token):
    line = column = None
    if hasattr(token, 'line'):
        line = token.line
        column = token.column
    elif hasattr(token, 'meta'):  # Tree with meta
        line = token.meta.line
        column = token.meta.column
    elif 'line' in token and 'column' in token:
        line = token['line']
        column = token['column']
    return {'rule': rule, 'value': value, 'line': line, 'column': column}
