import ply.lex as lex

states = (
    ('cartouche', 'exclusive'),
)

#
# Support for nested cartouche blocks
#


def t_CARTOUCHE_START(t):
    r'\\<open>'
    print('cartouche start', t.value)
    t.lexer.push_state('cartouche')  # Enter `cartouche` state
    t.lexer.cartouche_content = t.value
    t.lexer.cartouche_level = 1     # Start at nesting level 1


def t_cartouche_TEXT(t):
    r'[^\\]+'
    print('cartouche text', t.value)
    t.lexer.lineno += t.value.count('\n')
    t.lexer.cartouche_content += t.value


def t_cartouche_OPEN(t):
    r'\\<open>'
    print('cartouche open')
    t.lexer.cartouche_content += t.value
    t.lexer.cartouche_level += 1


def t_cartouche_CLOSE(t):
    r'\\<close>'
    t.lexer.cartouche_level -= 1
    t.lexer.cartouche_content += t.value
    if t.lexer.cartouche_level == 0:
        # Exit `cartouche` state when nesting level reaches 0
        t.value = t.lexer.cartouche_content
        t.type = "CARTOUCHE"  # Emit a CARTOUCHE token
        t.lineno = t.lexer.lineno
        t.column = find_column(t.lexer.lexdata, t)
        t.lexer.pop_state()
        return t


def t_cartouche_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    t.lexer.cartouche_content += t.value


def t_cartouche_error(t):
    print(f"Illegal character '{t.value[0]}' in cartouche")
    t.lexer.skip(1)


t_cartouche_ignore = ' \t'


# Define tokens for Isabelle syntax elements
tokens = (
    'OUTER_COMMENT',
    'CARTOUCHE',

    'RIGHTLEFTHARPOONS',
    'INFINITY',
    'SUBSETEQ',

    'VAR_CASE',
    'VAR_THESIS',

    'ABBREVIATION',
    'ALSO',
    'AND',
    'APPLY',
    'APPLY_END',
    'ARBITRARY',
    'ASSMS',
    'ASSUME',
    'ASSUMES',
    'AT',
    'AXIOMATIZATION',
    'BACKSLASH',
    'BANG',
    'BEGIN',
    'BINDER',
    'BOTTOM',
    'BY',
    'CASE',
    'CASES',
    'CHAPTER',
    'COINDUCT',
    'COLON',
    'COLONCOLON',
    'COMMA',
    'COMMENT_CARTOUCHE',
    'CONSIDER',
    'CONSTRAINS',
    'CONSTS',
    'CONTEXT',
    'COROLLARY',
    'DASH',
    'DATATYPE',
    'DECLARATION',
    'DECLARE',
    'DEFER',
    'DEFINE',
    'DEFINES',
    'DEFINITION',
    'DONE',
    'DOT',
    'END',
    'EQUALS',
    'EQUIV',
    'FALSE',
    'FIX',
    'FIXES',
    'FOLDED',
    'FOR',
    'FROM',
    'FUN',
    'FUNCTION',
    'GLOBAL_INTERPRETATION',
    'GT',
    'HAT',
    'HAVE',
    'HENCE',
    'HIDE_CLASS',
    'HIDE_CONST',
    'HIDE_FACT',
    'HIDE_TYPE',
    'IF',
    'IMPORTS',
    'IN',
    'INCLUDES',
    'INDUCT',
    'INDUCTION',
    'INDUCTIVE',
    'INFIX',
    'INFIXL',
    'INFIXR',
    'INPUT',
    'INSTANCE',
    'INSTANTIATION',
    'INTERPRET',
    'INTERPRETATION',
    'IS',
    'LEFT_BRACE',
    'LEFT_BRACKET',
    'LEFT_PAREN',
    'LEMMA',
    'LEMMAS',
    'LET',
    'LOCALE',
    'LT',
    'MARKER',
    'METHOD',
    'ML',
    'MODULE_NAME',
    'MONOS',
    'MOREOVER',
    'NEWLINE',
    'NEXT',
    'NITPICK',
    'NOTATION',
    'NOTE',
    'NOTES',
    'NO_NOTATION',
    'NO_SIMP',
    'NO_SYNTAX',
    'NO_TRANSLATIONS',
    'OBTAIN',
    'OBTAINS',
    'OOPS',
    'OPEN',
    'OPENING',
    'OVERLOADED',
    'PARAGRAPH',
    'PARTIAL_FUNCTION',
    'PERVASIVE',
    'PIPE',
    'PLUS',
    'PRED',
    'PREFER',
    'PRESUME',
    'PRIMREC',
    'PROOF',
    'PROPOSITION',
    'QED',
    'QUESTION_MARK',
    'RECORD',
    'RIGHT_BRACE',
    'RIGHT_BRACKET',
    'RIGHT_PAREN',
    'RULE',
    'SCHEMATIC_GOAL',
    'SECTION',
    'SEMICOLON',
    'SET',
    'SETUP',
    'SHOW',
    'SHOWS',
    'SLASH',
    'SORRY',
    'STAR',
    'STRUCTURE',
    'SUBGOAL',
    'SUBLOCALE',
    'SUBSECTION',
    'SUBSUBSECTION',
    'SUPPLY',
    'SYNTAX',
    'SYNTAX_DECLARATION',
    'TAKING',
    'TEXT',
    'THEN',
    'THEOREM',
    'THEORY',
    'THUS',
    'TRANSLATIONS',
    'TRUE',
    'TXT',
    'TYPE',
    'TYPEDECL',
    'TYPE_SYNONYM',
    'ULTIMATELY',
    'UNFOLDED',
    'UNFOLDING',
    'USING',
    'WHEN',
    'WHERE',
    'WITH',

    'SML',
    'OCAML',
    'HASKELL',
    'SCALA',
    'EVAL',

    'ALTSTRING',
    'GREEK',
    'LATIN',
    'LETTER',
    'STRING',
    'SUBSCRIPT',
    'SYM_FLOAT',
    'SYM_IDENT',
    'TERM_VAR',
    'TYPE_VAR',
    'VERBATIM',
    'UNDERSCORE',
    'FILE_PREFIX',

    'NAT',
    'ID',
    'LONG_IDENT',
    'SHORT_IDENT',
    'TYPE_IDENT',
)


def t_OUTER_COMMENT(t):
    r'\(\*[\s\S]*?\*\)'  # Match multiline comments
    t.lexer.lineno += t.value.count('\n')
    pass  # Ignore comments


def t_BOTTOM(t):
    r'\\<bottom>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_EQUIV(t):
    r'\\<equiv>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_NEWLINE(t):
    r'\\<newline>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_COMMENT_CARTOUCHE(t):
    r'\\<comment>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_MARKER(t):
    r'\\<\^marker>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_VAR_CASE(t):
    r'\?case'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_VAR_THESIS(t):
    r'\?thesis'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_GREEK(t):
    r'\\<alpha>|\\<beta>|\\<gamma>|\\<delta>|\\<epsilon>|\\<zeta>|\\<eta>|' \
            r'\\<theta>|\\<iota>|\\<kappa>|\\<mu>|\\<nu>|\\<xi>|\\<pi>|' \
            r'\\<rho>|\\<sigma>|\\<tau>|\\<upsilon>|\\<phi>|\\<chi>|\\<psi>|' \
            r'\\<omega>|\\<Gamma>|\\<Delta>|\\<Theta>|\\<Lambda>|\\<Xi>|' \
            r'\\<Pi>|\\<Sigma>|\\<Upsilon>|\\<Phi>|\\<Psi>|\\<Omega>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_RIGHTLEFTHARPOONS(t):
    r'\\<rightleftharpoons>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_INFINITY(t):
    r'\\<infinity>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_SUBSETEQ(t):
    r'\\<subseteq>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


reserved = {
        'Eval': 'EVAL',
        'False': 'FALSE',
        'Haskell': 'HASKELL',
        'ML': 'ML',
        'OCaml': 'OCAML',
        'SML': 'SML',
        'Scala': 'SCALA',
        'True': 'TRUE',
        'abbreviation': 'ABBREVIATION',
        'also': 'ALSO',
        'and': 'AND',
        'apply': 'APPLY',
        'apply_end': 'APPLY_END',
        'arbitrary': 'ARBITRARY',
        'assms': 'ASSMS',
        'assume': 'ASSUME',
        'assumes': 'ASSUMES',
        'at': 'AT',
        'axiomatization': 'AXIOMATIZATION',
        'begin': 'BEGIN',
        'binder': 'BINDER',
        'by': 'BY',
        'case': 'CASE',
        'cases': 'CASES',
        'chapter': 'CHAPTER',
        'coinduct': 'COINDUCT',
        'consider': 'CONSIDER',
        'constrains': 'CONSTRAINS',
        'consts': 'CONSTS',
        'context': 'CONTEXT',
        'corollary': 'COROLLARY',
        'datatype': 'DATATYPE',
        'declaration': 'DECLARATION',
        'declare': 'DECLARE',
        'defer': 'DEFER',
        'define': 'DEFINE',
        'defines': 'DEFINES',
        'definition': 'DEFINITION',
        'done': 'DONE',
        'end': 'END',
        'file_prefix': 'FILE_PREFIX',
        'fix': 'FIX',
        'fixes': 'FIXES',
        'folded': 'FOLDED',
        'for': 'FOR',
        'from': 'FROM',
        'fun': 'FUN',
        'function': 'FUNCTION',
        'global_interpretation': 'GLOBAL_INTERPRETATION',
        'have': 'HAVE',
        'hence': 'HENCE',
        'hide_class': 'HIDE_CLASS',
        'hide_const': 'HIDE_CONST',
        'hide_fact': 'HIDE_FACT',
        'hide_type': 'HIDE_TYPE',
        'if': 'IF',
        'imports': 'IMPORTS',
        'in': 'IN',
        'includes': 'INCLUDES',
        'induct': 'INDUCT',
        'induction': 'INDUCTION',
        'inductive': 'INDUCTIVE',
        'infix': 'INFIX',
        'infixl': 'INFIXL',
        'infixr': 'INFIXR',
        'input': 'INPUT',
        'instance': 'INSTANCE',
        'instantiation': 'INSTANTIATION',
        'interpret': 'INTERPRET',
        'interpretation': 'INTERPRETATION',
        'is': 'IS',
        'lemma': 'LEMMA',
        'lemmas': 'LEMMAS',
        'let': 'LET',
        'locale': 'LOCALE',
        'method': 'METHOD',
        'module_name': 'MODULE_NAME',
        'monos': 'MONOS',
        'moreover': 'MOREOVER',
        'next': 'NEXT',
        'nitpick': 'NITPICK',
        'no_notation': 'NO_NOTATION',
        'no_simp': 'NO_SIMP',
        'no_syntax': 'NO_SYNTAX',
        'no_translations': 'NO_TRANSLATIONS',
        'notation': 'NOTATION',
        'note': 'NOTE',
        'notes': 'NOTES',
        'obtain': 'OBTAIN',
        'obtains': 'OBTAINS',
        'oops': 'OOPS',
        'open': 'OPEN',
        'opening': 'OPENING',
        'overloaded': 'OVERLOADED',
        'paragraph': 'PARAGRAPH',
        'partial_function': 'PARTIAL_FUNCTION',
        'pervasive': 'PERVASIVE',
        'pred': 'PRED',
        'prefer': 'PREFER',
        'presume': 'PRESUME',
        'primrec': 'PRIMREC',
        'proof': 'PROOF',
        'proposition': 'PROPOSITION',
        'qed': 'QED',
        'record': 'RECORD',
        'rule': 'RULE',
        'schematic_goal': 'SCHEMATIC_GOAL',
        'section': 'SECTION',
        'set': 'SET',
        'setup': 'SETUP',
        'show': 'SHOW',
        'shows': 'SHOWS',
        'sorry': 'SORRY',
        'structure': 'STRUCTURE',
        'subgoal': 'SUBGOAL',
        'sublocale': 'SUBLOCALE',
        'subsection': 'SUBSECTION',
        'subsubsection': 'SUBSUBSECTION',
        'supply': 'SUPPLY',
        'syntax': 'SYNTAX',
        'syntax_declaration': 'SYNTAX_DECLARATION',
        'taking': 'TAKING',
        'text': 'TEXT',
        'then': 'THEN',
        'theorem': 'THEOREM',
        'theory': 'THEORY',
        'thus': 'THUS',
        'translations': 'TRANSLATIONS',
        'txt': 'TXT',
        'type': 'TYPE',
        'type_synonym': 'TYPE_SYNONYM',
        'typedecl': 'TYPEDECL',
        'ultimately': 'ULTIMATELY',
        'unfolded': 'UNFOLDED',
        'unfolding': 'UNFOLDING',
        'using': 'USING',
        'when': 'WHEN',
        'where': 'WHERE',
        'with': 'WITH',
    }


def t_SHORT_IDENT(t):
    r'[a-zA-Z](_?\d*[a-zA-Z_\']*)*'
    if t.value in reserved:
        t.type = reserved[t.value]
    else:
        t.type = 'ID'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LONG_IDENT(t):
    r'([a-zA-Z](_?\d*[a-zA-Z\']*)*)(\.([a-zA-Z\'](_?\d*[a-zA-Z\']*)*))+'
    if t.value in reserved:
        t.type = reserved[t.value]
    else:
        t.type = 'ID'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_SYM_IDENT(t):
    r'[!#$%&*+\-/<>?@^_`|~]+[a-zA-Z][a-zA-Z0-9]*'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9\']*(\\<\^sub>[a-zA-Z0-9_]*)?'
    t.type = reserved.get(t.value, 'ID')    # Check for reserved words
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_ALTSTRING(t):
    r'`[^`]*`'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_VERBATIM(t):
    r'{\*.*\*}'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LETTER(t):
    r'[a-zA-Z]'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_SUBSCRIPT(t):
    r'\\<\^sub>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LATIN(t):
    r'[a-zA-Z]'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LEFT_BRACE(t):
    r'\{'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_RIGHT_BRACE(t):
    r'\}'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_SLASH(t):
    r'/'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


t_BANG = r'!'
t_COLON = r':'
t_COMMA = r','
t_DASH = r'-'
t_DOT = r'\.'
t_EQUALS = r'='
t_PLUS = r'\+'
t_QUESTION_MARK = r'\?'
t_SEMICOLON = r';'
t_UNDERSCORE = r'_'


def t_COLONCOLON(t):
    r'::'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LEFT_PAREN(t):
    r'\('
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_RIGHT_PAREN(t):
    r'\)'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LEFT_BRACKET(t):
    r'\['
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_RIGHT_BRACKET(t):
    r'\]'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_PIPE(t):
    r'\|'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_STAR(t):
    r'\*'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_BACKSLASH(t):
    r'\\'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LT(t):
    r'<'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_HAT(t):
    r'\^'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_GT(t):
    r'>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_TYPE_IDENT(t):
    r'\'[a-zA-Z](_?\d*[a-zA-Z_\']*)*'
    t.type = 'TYPE_IDENT'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


# Token definitions
t_NAT = r'\d+'
t_SYM_FLOAT = r'(\d+(\.\d+)+|\.\d+)'
t_TERM_VAR = r'\?[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*'
t_TYPE_VAR = r"'[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*"
t_STRING = r'"[^"]*"'

# Define sub-parts for more complex tokens
latin_letters = r'[a-zA-Z]'

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3
#


def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


# Define ignored characters (spaces and tabs)
t_ignore = ' \t'


# Define a function to handle errors
def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.lexer.skip(1)


def find_column(input, token):
    return get_column(input, token.lexpos)


def get_column(input, lexpos):
    line_start = input.rfind('\n', 0, lexpos) + 1
    return (lexpos - line_start) + 1


def reset_lexer(lexer, new_input=None):
    lexer.lineno = 0  # Reset line number
    lexer.lexpos = 0  # Reset current position

    if new_input is not None:
        lexer.input(new_input)  # Set new input for the lexer


lexer = lex.lex(debug=True)
