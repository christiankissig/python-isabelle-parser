from isabelle_parser import thy_lexer


def test_lex_quoted_string():
    input = """
lemma somelemma:
    assumes "P"
    shows "Q"
    """
    thy_lexer.input(input)
    tokens = []
    while True:
        tok = thy_lexer.token()
        if not tok:
            break
        tokens.append(tok)
    assert len(tokens) > 0
    assert tokens[0].value == 'lemma'
    assert tokens[0].type == 'LEMMA'
    assert tokens[1].value == 'somelemma'
    assert tokens[1].type == 'ID'
    assert tokens[2].value == ':'
    assert tokens[2].type == 'COLON'
    assert tokens[3].value == 'assumes'
    assert tokens[3].type == 'ASSUMES'
    assert tokens[4].value == '"P"'
    assert tokens[4].type == 'QUOTED_STRING'
    assert tokens[5].value == 'shows'
    assert tokens[5].type == 'SHOWS'
    assert tokens[6].value == '"Q"'
    assert tokens[6].type == 'QUOTED_STRING'


def test_lex_theory():
    input = """
theory test_theory
imports
    Main
begin
end
    """
    thy_lexer.input(input)
    tokens = []
    while True:
        tok = thy_lexer.token()
        if not tok:
            break
        tokens.append(tok)
    assert len(tokens) > 0
    assert tokens[0].value == 'theory'
    assert tokens[0].type == 'THEORY'


def test_lex_lemma():
    input = """
lemma I7_preserves_pre_block_global_pre:
assumes 1: "block_cond t' ta ms \\<sigma>"
    """
    thy_lexer.input(input)
    tokens = []
    while True:
        tok = thy_lexer.token()
        if not tok:
            break
        tokens.append(tok)
    assert len(tokens) > 0
    assert tokens[0].value == 'lemma'
    assert tokens[0].type == 'LEMMA'


