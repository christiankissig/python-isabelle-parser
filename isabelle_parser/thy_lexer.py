import ply.lex as lex

# Define tokens for Isabelle syntax elements
tokens = (
    'OUTER_COMMENT',
    'CARTOUCHE',

    'AND',
    'APPLY',
    'ASSMS',
    'ASSUME',
    'ASSUMES',
    'AXIOMATIZATION',
    'BACKSLASH',
    'BANG',
    'BEGIN',
    'BINDER',
    'BY',
    'COLON',
    'COMMA',
    'COMMENT_CARTOUCHE',
    'CONSTRAINS',
    'DASH',
    'DEFINES',
    'DONE',
    'DOT',
    'END',
    'EQ',
    'EQUALS',
    'FIXES',
    'FOR',
    'FUN',
    'FUNCTION',
    'GLOBAL_INTERPRETATION',
    'GT',
    'HAT',
    'HAVE',
    'IF',
    'IMPORTS',
    'INFIX',
    'INFIXL',
    'INFIXR',
    'INTERPRET',
    'INTERPRETATION',
    'IS',
    'LEFT_BRACKET',
    'LEFT_PAREN',
    'LEMMA',
    'LOCALE',
    'LT',
    'METHOD',
    'NOTES',
    'OPENING',
    'PLUS',
    'PRIMREC',
    'PROOF',
    'QUESTION_MARK',
    'RIGHT_BRACKET',
    'RIGHT_PAREN',
    'SECTION',
    'SEMICOLON',
    'SHOW',
    'SHOWS',
    'SORRY',
    'STAR',
    'STRUCTURE',
    'SUBGOAL',
    'SUBLOCALE',
    'TEXT',
    'THEN',
    'THEORY',
    'TYPEDECL',
    'TYPE_SYNONYM',
    'USING',
    'WHERE',
    'PIPE',

    'ALTSTRING',
    'GREEK',
    'LATIN',
    'LETTER',
    'LONG_IDENT',
    'NAT',
    'SHORT_IDENT',
    'STRING',
    'SUBSCRIPT',
    'SYM_FLOAT',
    'SYM_IDENT',
    'TERM_VAR',
    'TYPE_IDENT',
    'TYPE_VAR',
    'VERBATIM',
    'UNDERSCORE',

    'QUOTED_STRING',
    'ID',
)


def t_OUTER_COMMENT(t):
    r'\(\*[\s\S]*?\*\)'  # Match multiline comments
    t.lexer.lineno += t.value.count('\n')
    pass  # Ignore comments


def t_CARTOUCHE(t):
    r'\\<open>[\s\S]*?\\<close>'
    t.lexer.lineno += t.value.count('\n')
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_COMMENT_CARTOUCHE(t):
    r'\\<comment>'
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


reserved = {
        'and': 'AND',
        'apply': 'APPLY',
        'assms': 'ASSMS',
        'assume': 'ASSUME',
        'assumes': 'ASSUMES',
        'axiomatization': 'AXIOMATIZATION',
        'begin': 'BEGIN',
        'binder': 'BINDER',
        'by': 'BY',
        'constrains': 'CONSTRAINS',
        'defines': 'DEFINES',
        'done': 'DONE',
        'end': 'END',
        'eq': 'EQ',
        'fixes': 'FIXES',
        'for': 'FOR',
        'fun': 'FUN',
        'function': 'FUNCTION',
        'global_interpretation': 'GLOBAL_INTERPRETATION',
        'have': 'HAVE',
        'if': 'IF',
        'imports': 'IMPORTS',
        'infix': 'INFIX',
        'infixl': 'INFIXL',
        'infixr': 'INFIXR',
        'interpret': 'INTERPRET',
        'interpretation': 'INTERPRETATION',
        'is': 'IS',
        'lemma': 'LEMMA',
        'locale': 'LOCALE',
        'method': 'METHOD',
        'notes': 'NOTES',
        'opening': 'OPENING',
        'primrec': 'PRIMREC',
        'proof': 'PROOF',
        'section': 'SECTION',
        'show': 'SHOW',
        'shows': 'SHOWS',
        'sorry': 'SORRY',
        'structure': 'STRUCTURE',
        'subgoal': 'SUBGOAL',
        'sublocale': 'SUBLOCALE',
        'text': 'TEXT',
        'then': 'THEN',
        'theory': 'THEORY',
        'type_synonym': 'TYPE_SYNONYM',
        'typedecl': 'TYPEDECL',
        'using': 'USING',
        'where': 'WHERE',
}


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


def t_SHORT_IDENT(t):
    r'[a-zA-Z](_?\d*[a-zA-Z]*)*'
    if t.value in reserved:
        t.type = reserved[t.value]
    else:
        t.type = 'ID'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_LONG_IDENT(t):
    r'([a-zA-Z](_?\d*[a-zA-Z]*)*)(\.([a-zA-Z](_?\d*[a-zA-Z]*)*))+'
    if t.value in reserved:
        t.type = reserved[t.value]
    else:
        t.type = 'ID'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_SYM_IDENT(t):
    r'[!#$%&*+\-/<=>?@^_`|~]+<([a-zA-Z](_?\d*[a-zA-Z]*)*)>'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_QUOTED_STRING(t):
    r'"[^"]*"'
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




t_BANG = r'!'
t_AND = r'and'
t_APPLY = r'apply'
t_ASSMS = r'assms'
t_ASSUME = r'assume'
t_ASSUMES = r'assumes'
t_BEGIN = r'begin'
t_BY = r'by'
t_COLON = r':'
t_COMMA = r','
t_DASH = r'-'
t_DONE = r'done'
t_DOT = r'\.'
t_END = r'end'
t_EQUALS = r'='
t_HAVE = r'have'
t_IMPORTS = r'imports'
t_UNDERSCORE = r'_'

t_LEMMA = r'lemma'
t_METHOD = r'method'
t_PLUS = r'\+'
t_PROOF = r'proof'
t_QUESTION_MARK = r'\?'
t_SEMICOLON = r';'
t_SHOW = r'show'


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


def t_SHOWS(t):
    r'shows'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


def t_SORRY(t):
    r'sorry'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


t_SUBGOAL = r'subgoal'
t_THEN = r'then'


def t_THEORY(t):
    r'theory'
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


t_USING = r'using'

# Token definitions
t_NAT = r'\d+'
t_SYM_FLOAT = r'(\d+(\.\d+)+|\.\d+)'
t_TERM_VAR = r'\?[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*'
t_TYPE_IDENT = r"'\w+"
t_TYPE_VAR = r"'[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*"
t_STRING = r'"[^"]*"'

# Define sub-parts for more complex tokens
latin_letters = r'[a-zA-Z]'
subscript = r'\\<\^sub>'

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3
#


def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'ID')    # Check for reserved words
    t.lineno = t.lexer.lineno
    t.column = find_column(t.lexer.lexdata, t)
    return t


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
