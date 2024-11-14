import ply.yacc as yacc
import logging

from .error import ParsingError
from .thy_lexer import lexer, reset_lexer, get_column, tokens

__all__ = ['tokens']


logger = logging.getLogger(__name__)


#
# Top level
#

def p_theory_file(p):
    '''theory_file : theory_block
                   | section_block theory_file
                   | text_block theory_file'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_theory_block(p):
    '''theory_block : THEORY ID imports_opt BEGIN content END'''
    global source
    imports = p[3]
    p[0] = (
        'theory',
        {
            'name': p[2],
            'imports': imports[1],
            'content': p[5],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        }
    )


def p_imports_opt(p):
    '''imports_opt : IMPORTS import_list
                   | empty'''
    p[0] = ('imports', p[2]) if len(p) > 2 else ('imports', [])


def p_import_list(p):
    '''import_list : QUOTED_STRING import_list
                   | ID import_list
                   | ID'''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    else:
        p[0] = [p[1]]


def p_content(p):
    '''content : statement content
               | empty'''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    else:
        p[0] = []


def p_theory(p):
    '''theory : statement'''
    p[0] = p[1]

def p_statement(p):
    '''statement : axiomatization_block
                 | fun_block
                 | interpretation_block
                 | lemma_block
                 | locale_block
                 | method_block
                 | notation_block
                 | section_block
                 | text_block
                 | type_synonym
                 | typedecl'''
    p[0] = p[1]


def p_method_block(p):
    '''method_block : METHOD method_name EQUALS instruction'''
    p[0] = ('method', {
        'name': p[2],
        'instruction': p[4],
    })


# Lemma name
def p_method_name(p):
    '''method_name : ID
                   | INDUCT
                   | ID DOT ID
                   | ID DOT ID DOT ID
                   | QUOTED_STRING'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = ".".join(p[1:])


def p_instruction(p):
    '''instruction : single_instruction
                   | single_instruction instruction_modifier
                   | single_instruction instruction_modifier COMMA instruction
                   | single_instruction SEMICOLON instruction
                   | single_instruction COMMA instruction
                   | LEFT_PAREN instruction RIGHT_PAREN
                   | LEFT_PAREN instruction RIGHT_PAREN instruction_modifier'''
    p[0] = ('instruction', *p[1:])


def p_instruction_modifier(p):
    '''instruction_modifier : PLUS
                            | QUESTION_MARK'''
    p[0] = p[1]


def p_single_instruction(p):
    '''single_instruction : LEFT_PAREN ID method_args RIGHT_PAREN
                          | LEFT_PAREN ID method_args RIGHT_PAREN instruction_modifier
                          | ID method_args
                          | ID
                          '''
    global source
    if len(p) == 2:
        p[0] = ('single_instruction',
                {
                    'method': p[1],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                })
    elif len(p) == 3:
        p[0] = ('single_instruction',
                {
                    'method': p[1],
                    'args': p[2],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                })
    elif len(p) == 5:
        p[0] = ('single_instruction',
                {
                    'method': p[2],
                    'args': p[3],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                })
    elif len(p) == 6:
        p[0] = ('single_instruction',
                {
                    'method': p[2],
                    'args': p[3],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    'modifier': p[5],
                })


def p_method_args(p):
    '''method_args : ID COLON method_args
                   | method_arg method_args
                   | method_arg COMMA method_args
                   | method_arg
                   | empty'''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    elif len(p) == 4:
        p[0] = [p[1]] + p[3]
    elif len(p) == 5:
        p[0] = [p[1], p[2], p[3]] + p[4]
    else:
        p[0] = []


def p_method_arg(p):
    '''method_arg : ID LEFT_PAREN NAT RIGHT_PAREN
                  | ID DOT ID
                  | GREEK DOT ID
                  | ID DOT ID LEFT_PAREN NAT RIGHT_PAREN
                  | GREEK DOT ID LEFT_PAREN NAT RIGHT_PAREN
                  | ID DOT ID DOT ID LEFT_PAREN NAT RIGHT_PAREN
                  | QUOTED_STRING
                  | ID'''
    p[0] = "".join(p[1:])


def p_lemma_block(p):
    '''lemma_block : LEMMA ID COLON QUOTED_STRING proof_prove
                   | LEMMA ID COLON fixes assumes shows proof_prove'''
    p[0] = ('lemma', {
        'name': p[2],
        'statement': p[4] if len(p) == 6 else None,
        'fixes': p[4] if len(p) == 8 else None,
        'assumes': p[5] if len(p) == 8 else None,
        'shows': p[6] if len(p) == 8 else None,
        'proof': p[7] if len(p) == 8 else p[5],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_fixes(p):
    '''fixes : FIXES var_list_nosep
             | empty'''
    p[0] = p[2] if len(p) == 3 else []


def p_var_list_nosep(p):
    '''var_list_nosep : var var_list_nosep
                      | var'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_assumes(p):
    '''assumes : ASSUME assumption
               | ASSUMES assumptions_list
               | empty'''
    if len(p) == 2:
        p[0] = []
    elif isinstance(p[2], list):
        p[0] = ('assumes', p[2])
    else:
        p[0] = ('assumes', [p[2]])


def p_assumptions_list(p):
    '''assumptions_list : assumption AND assumptions_list
                        | assumption'''
    if len(p) > 2:
        p[0] = [p[1]] + p[3]
    else:
        p[0] = [p[1]]


def p_assumption(p):
    '''assumption : QUOTED_STRING
                  | NAT COLON QUOTED_STRING'''
    p[0] = ('assumption',
            {
                'id': p[1] if len(p) > 2 else None,
                'text': p[1] if len(p) == 2 else p[3],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_shows(p):
    '''shows : SHOWS QUOTED_STRING'''
    p[0] = ('shows', p[2])


def p_subgoals(p):
    '''subgoals : subgoal subgoals
                | subgoal'''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    else:
        p[0] = [p[1]]


def p_subgoal(p):
    '''subgoal : SUBGOAL QUOTED_STRING apply_block'''
    p[0] = ('subgoal', {
        'name': p[2],
        'apply_block': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.7
#


def p_type(p):
    '''type : QUOTED_STRING
            | GREEK
            | ID'''
    p[0] = ('type', p[1])


def p_term(p):
    '''term : QUOTED_STRING
            | GREEK
            | ID'''
    p[0] = ('term', p[1])


def p_prop(p):
    '''prop : QUOTED_STRING
            | VAR_CASE
            | VAR_THESIS
            | FALSE
            | TRUE'''
    p[0] = ('prop', p[1])


def p_inst(p):
    '''inst : UNDERSCORE
            | term'''
    p[0] = ('inst', p[1])


def p_insts(p):
    '''insts : inst insts
             | inst'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_typespec(p):
    '''typespec : ID
                | typeargs ID'''
    p[0] = ('typespec', {
                'typeargs': p[1] if len(p) == 3 else [],
                'name': p[2] if len(p) == 3 else p[1],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


def p_typearg(p):
    '''typearg : ID
                | ID COLON COLON ID'''
    p[0] = ('typearg', {
                'name': p[1],
                'sort': p[4] if len(p) > 2 else None,
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


# moved empty case to p_typespec in order to avoid parsing error
def p_typeargs(p):
    '''typeargs : typearg
                | typearg COMMA typeargs
                | LEFT_PAREN typeargs RIGHT_PAREN'''
    if len(p) == 2:
        p[0] = [p[1]]
    elif len(p) == 4:
        if p[2] == ',':
            p[0] = [p[1]] + p[3]
        else:
            p[0] = p[2]

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.8
#


def p_vars(p):
    '''vars : var AND vars
            | var vars
            | var'''
    p[0] = [p[1]]
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    elif len(p) == 4:
        p[0] = [p[1]] + p[3]


def p_var(p):
    '''var : ID COLON COLON ID
           | GREEK COLON COLON ID
           | ID COLON COLON QUOTED_STRING
           | GREEK COLON COLON QUOTED_STRING
           | names COLON COLON ID
           | names COLON COLON QUOTED_STRING
           | ID COLON COLON ID mixfix
           | GREEK COLON COLON ID mixfix
           | ID COLON COLON QUOTED_STRING mixfix
           | GREEK COLON COLON QUOTED_STRING mixfix
           | ID mixfix
           | ID
           | names'''
    if len(p) == 2:
        names = p[1] if isinstance(p[1], list) else [p[1]]
        mixfix = None
        var_type = None
    elif len(p) == 3:
        names = [p[1]]
        mixfix = p[2]
        var_type = None
    elif len(p) == 5:
        names = p[1]
        var_type = p[3]
        mixfix = None
    elif len(p) > 5:
        names = p[1]
        var_type = p[4]
        mixfix = p[5]
    else:
        mixfix = None
        var_type = None
        if isinstance(p[1], list):
            names = p[1]
        else:
            names = [p[1]]
    p[0] = ('var', {
                'names': names,
                'type': var_type,
                'mixfix': mixfix,
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


def p_props(p):
    '''props : prop_list_with_pat
             | thmdecl prop_list_with_pat'''
    p[0] = ('props', {
                'thmdecl': p[1] if len(p) == 3 else None,
                'props': p[1] if len(p) == 2 else p[2],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


def p_prop_list_with_pat(p):
    '''prop_list_with_pat : prop prop_pat prop_list
                          | prop prop_list
                          | prop'''
    p[0] = [(p[1], p[2] if len(p) > 2 else None)] + p[3] if len(p) > 2 else [p[1]]


def p_names(p):
    '''names : ID AND names
             | ID'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_name_list(p):
    '''name_list : ID
                 | ID name_list'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_names_list(p):
    '''names_list : ID
                  | ID names'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_prop_pat(p):
    '''prop_pat : LEFT_PAREN prop_pat_terms RIGHT_PAREN'''
    p[0] = ('prop_pat', p[2])


def p_prop_pat_terms(p):
    '''prop_pat_terms : prop_pat_term
                      | prop_pat_term prop_pat_terms'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_prop_pat_term(p):
    '''prop_pat_term : IS ID
                     | IS QUOTED_STRING'''
    p[0] = ('prop is', p[2])


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.1
#


def p_name(p):
    '''name : ID
            | QUOTED_STRING'''
    p[0] = p[1]


def p_par_name(p):
    '''par_name : LEFT_PAREN name RIGHT_PAREN'''
    p[0] = ('par_name', {
        'name': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.9
#


def p_thmdecl(p):
    '''thmdecl : thmbind COLON'''
    p[0] = ('thmdecl', p[1])


def p_thmdef(p):
    '''thmdef : thmbind EQ'''
    p[0] = ('thmdef', p[1])


def p_thm(p):
    '''thm : NAT
           | ID attributes
           | ID
           | CARTOUCHE
           | assms
           | attributes'''
    if len(p) == 2:
        p[0] = ('thm', {
            'name': p[1] if isinstance(p[1], str) else None,
            'attributes': None if isinstance(p[1], str) else p[1],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 3:
        p[0] = ('thm', {
            'name': p[1],
            'attributes': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_thms(p):
    '''thms : thm
            | assms
            | thm thms'''
    p[0] = [p[1]] + p[2] if len(p) == 3 else [p[1]]


def p_thmbind(p):
    '''thmbind : ID
               | ID attributes
               | attributes'''
    if len(p) == 2:
        if isinstance(p[1], str):
            p[0] = ('thmbind', {
                'name': p[1] if isinstance(p[1], str) else None,
                'attributes': None if isinstance(p[1], str) else p[1],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })
        elif len(p) == 3:
            p[0] = ('thmbind', {
                'name': p[1],
                'attributes': p[2],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


def p_attributes(p):
    '''attributes : LEFT_BRACKET attributes_list RIGHT_BRACKET'''
    p[0] = p[2]


def p_attributes_list(p):
    '''attributes_list : empty
                       | attribute
                       | attribute COMMA attributes_list'''
    if len(p) == 2:
        if p[1] is None:
            p[0] = []
        else:
            p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_attribute(p):
    '''attribute : ID args'''
    p[0] = (p[1], p[2])


def p_args(p):
    '''args : empty
            | arg
            | arg args'''
    if len(p) == 2:
        if p[1] is None:
            p[0] = []
        else:
            p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_arg(p):
    '''arg : ID
           | LEFT_PAREN args RIGHT_PAREN
           | LEFT_BRACKET args RIGHT_BRACKET'''
    if len(p) == 2:
        p[0] = ('arg', {
                'value': p[1],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })
    else:
        p[0] = ('arg', {
                'args': p[2],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.10
#

def p_for_fixes(p):
    '''for_fixes : FOR vars
                 | empty'''
    if len(p) == 2:
        return None
    else:
        p[0] = ('for', p[2])


def p_multi_specs(p):
    '''multi_specs : structured_spec
                   | structured_spec PIPE multi_specs'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_structured_spec(p):
    '''structured_spec : ID spec_prems
                       | ID spec_prems for_fixes
                       | QUOTED_STRING spec_prems
                       | QUOTED_STRING spec_prems for_fixes
                       | thmdecl ID spec_prems for_fixes
                       | thmdecl QUOTED_STRING spec_prems for_fixes'''
    if len(p) == 3:
        p[0] = ('structured_spec', {
            'thmdecl': None,
            'prop': p[1],
            'spec_prems': p[2],
            'for_fixes': [],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 4:
        p[0] = ('structured_spec', {
            'thmdecl': None,
            'prop': p[1],
            'spec_prems': p[2],
            'for_fixes': p[3],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    else:
        p[0] = ('structured_spec', {
            'thmdecl': p[1],
            'prop': p[2],
            'spec_prems': p[3],
            'for_fixes': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_spec_prems(p):
    '''spec_prems : empty
                  | IF prop_list'''
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = ('if', p[2])


def p_prop_list(p):
    '''prop_list : prop
                 | prop prop_list'''
    p[0] = [p[1]] + p[2] if len(p) == 3 else [p[1]]


def p_specification(p):
    '''specification : vars WHERE multi_specs'''
    p[0] = ('specification', {
        'vars': p[1],
        'multi_specs': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


# TODO p75
def p_antiquotation_body(p):
    '''antiquotation_body : ID'''
    p[0] = ('antiquotation_body', {
        'type': p[1],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.2
#


def p_antiquotation(p):
    '''antiquotation : AT LEFT_BRACE antiquotation_body RIGHT_BRACE
                     | SLASH LT HAT ID GT CARTOUCHE
                     | CARTOUCHE'''
    p[0] = ('antiquotation', {
        'body': p[3] if len(p) == 5 else "".join(p[1:]),
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.1
#


def p_section_block(p):
    '''section_block : SECTION CARTOUCHE'''
    p[0] = ('section', p[2])


def p_text_block(p):
    '''text_block : TEXT CARTOUCHE'''
    p[0] = ('text', p[2])


def p_comment_block(p):
    '''comment_block : COMMENT_CARTOUCHE CARTOUCHE'''
    p[0] = ('comment', p[2])


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.5
#


def p_rules(p):
    '''rules : rule
             | rule SEMICOLON rules'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_rule(p):
    '''rule : body
            | ID COLON body
            | antiquotation COLON body'''
    if len(p) == 2:
        p[0] = ('rule', {
            'name': None,
            'body': p[1],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 3:
        p[0] = ('rule', {
            'name': p[1],
            'body': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_body(p):
    '''body : concatenation
            | concatenation PIPE body'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_concatenation(p):
    '''concatenation : atom_list
                     | atom_list STAR atom
                     | atom_list PLUS atom_list'''

    p[0] = ('concatenation', {
        'atoms': p[1],
        'star': p[2] if len(p) == 4 else None,
        'plus': p[3] if len(p) == 4 else None,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })

def p_atom_list(p):
    '''atom_list : atom
                 | atom QUESTION_MARK
                 | atom atom_list
                 | atom QUESTION_MARK atom_list'''
    if len(p) == 2:
        p[0] = [('atom', {'atom': p[1], 'question_mark': False})]
    elif len(p) == 3:
        if p[2] == '?':
            p[0] = [('atom', {'atom': p[1], 'question_mark': True})]
        else:
            p[0] = [('atom', {'atom': p[1], 'question_mark': False})] + p[2]
    else:
        p[0] = [('atom', {'atom': p[1], 'question_mark': True})] + p[2]


def p_atom(p):
    '''atom : LEFT_PAREN RIGHT_PAREN
            | LEFT_PAREN body RIGHT_PAREN
            | ID
            | QUOTED_STRING
            | antiquotation
            | AT QUOTED_STRING
            | AT antiquotation
            | NEWLINE'''
    if len(p) == 4 or (p[1] == '(' and p[2] == ')'):
        p[0] = ('atom', {
            'body': p[2] if len(p) == 4 else None,
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 2:
        p[0] = ('atom', {
            'name': p[1],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    else:
        p[0] = ('atom', {
            'at': len(p) == 3,
            'name': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.3
#


def p_includes(p):
    '''includes : INCLUDES names_list'''
    p[0] = ('includes', p[2])


def p_opening(p):
    '''opening : OPENING names_list'''
    p[0] = ('opening', p[2])


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.5
#


def p_axiomatization_block(p):
    '''axiomatization_block : AXIOMATIZATION
                            | AXIOMATIZATION vars
                            | AXIOMATIZATION WHERE axiomatization
                            | AXIOMATIZATION vars WHERE axiomatization'''
    if len(p) == 4:
        axiomatization = p[3]
    elif len(p) == 5:
        axiomatization = p[4]
    else:
        axiomatization = None
    p[0] = ('axiomatization', {
        'vars': p[2] if len(p) == 3 or len(p) == 5 else None,
        'axiomatization': axiomatization,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_axiomatization(p):
    '''axiomatization : axiomatization_header spec_prems for_fixes'''
    p[0] = ('axiomatization', {
        'header': p[1],
        'spec_prems': p[2],
        'for_fixes': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_axiomatization_header(p):
    '''axiomatization_header : thmdecl ID
                             | thmdecl QUOTED_STRING
                             | thmdecl ID AND axiomatization_header
                             | thmdecl QUOTED_STRING AND axiomatization_header'''
    if len(p) == 3:
        p[0] = [(p[1], p[2])]
    else:
        p[0] = [(p[1], p[2])] + p[4]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.1
#


# move empty case of for_fixes here to avoid parsing error
def p_locale_expr(p):
    '''locale_expr : instance_list for_fixes'''
    p[0] = ('locale_expr', {
        'instances': p[1],
        'for_fixes': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_instance_list(p):
    '''instance_list : instance
                     | instance PLUS instance_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_instance(p):
    '''instance : ID
                | ID pos_insts
                | ID name_insts
                | qualifier COLON ID pos_insts
                | qualifier COLON ID name_insts'''
    if len(p) == 2:
        p[0] = ('instance', {
            'name': p[1],
            'insts': ('pos_insts', []),
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 3:
        p[0] = ('instance', {
            'name': p[1],
            'insts': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 4:
        p[0] = ('instance', {
            'qualifier': p[1],
            'name': p[3],
            'insts': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_qualifier(p):
    '''qualifier : ID
                 | QUOTED_STRING
                 | ID QUESTION_MARK
                 | QUOTED_STRING QUESTION_MARK'''
    p[0] = ('qualifier', {'name': p[1], 'question_mark': len(p) == 3})


def p_pos_insts(p):
    '''pos_insts : UNDERSCORE
                 | BOTTOM
                 | ID
                 | QUOTED_STRING
                 | GREEK
                 | UNDERSCORE pos_insts
                 | ID pos_insts
                 | QUOTED_STRING pos_insts
                 | GREEK pos_insts'''
    if len(p) == 2:
        p[0] = ('pos_insts', [p[1]])
    else:
        p[0] = ('pos_insts', [p[1]] + p[2][1])


def p_name_insts(p):
    '''name_insts : WHERE name_insts_list'''
    p[0] = ('name_insts', p[2])


def p_name_insts_list(p):
    '''name_insts_list : ID EQUALS ID
                       | ID EQUALS QUOTED_STRING
                       | ID EQUALS ID name_insts_list
                       | ID EQUALS QUOTED_STRING name_insts_list'''
    if len(p) == 2:
        p[0] = [('equals', p[1], p[3])]
    else:
        p[0] = [('equals', p[1], p[3])] + p[3]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.2
#


def p_locale_block(p):
    '''locale_block : LOCALE ID
                    | LOCALE ID BEGIN content END
                    | LOCALE ID comment_block BEGIN content END
                    | LOCALE ID EQ locale
                    | LOCALE ID EQ locale BEGIN content END'''
    global source
    if len(p) == 3:
        p[0] = ('locale', {
            'name': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 6:
        p[0] = ('locale', {
            'name': p[2],
            'locale_theory': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 7:
        p[0] = ('locale', {
            'name': p[2],
            'comment': p[3],
            'locale_theory': p[5],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 5:
        p[0] = ('locale', {
            'name': p[2],
            'locale': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 8:
        p[0] = ('locale', {
            'name': p[2],
            'locale': p[4],
            'locale_theory': p[6],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_locale(p):
    '''locale : context_elem_list
              | opening
              | opening PLUS context_elem_list
              | locale_expr
              | locale opening
              | locale opening PLUS context_elem_list
              | locale_expr opening PLUS context_elem_list'''
    p[0] = ('locale', p[1:])


def p_context_elem_list(p):
    '''context_elem_list : context_elem
                         | context_elem context_elem_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_context_elem(p):
    '''context_elem : FIXES vars
                    | CONSTRAINS name_type_list
                    | ASSUMES prop_list
                    | DEFINES defines_list
                    | NOTES notes_list'''
    p[0] = ('context_elem', {
               'type': p[1],
               'content': p[2],
               'line': p.lineno(1),
               'column': get_column(source, p.lexpos(1)) if source else -1,
                })


def p_name_type_list(p):
    '''name_type_list : ID COLON COLON ID
                      | ID COLON COLON ID AND name_type_list'''
    if len(p) == 4:
        p[0] = [(p[1], p[4])]
    else:
        p[0] = [(p[1], p[4])] + p[6]


def p_defines_list(p):
    '''defines_list : defines_list_element
                    | defines_list_element AND defines_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_defines_list_element(p):
    '''defines_list_element : ID
                            | QUOTED_STRING
                            | thmdecl ID
                            | thmdecl QUOTED_STRING
                            | ID prop_pat
                            | QUOTED_STRING prop_pat
                            | thmdecl ID prop_pat
                            | thmdecl QUOTED_STRING prop_pat'''
    if len(p) == 2:
        p[0] = ('definition', {
                    'prop': p[1],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })
    elif len(p) == 3:
        p[0] = ('definition', {
                    'thmdecl': p[1] if p[1][0] == 'thmdecl' else None,
                    'prop': p[2] if p[1][0] == 'thmdecl' else p[1],
                    'prop_pat': None if p[1][0] == 'thmdecl' else p[2],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })
    elif len(p) == 4:
        p[0] = ('definition', {
                    'thmdecl': p[1],
                    'prop': p[2],
                    'prop_pat': p[3],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })


def p_notes_list(p):
    '''notes_list : notes_list_element
                  | notes_list_element AND notes_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_notes_list_element(p):
    '''notes_list_element : thmdef thms
                          | thms'''
    if len(p) == 2:
        p[0] = ('note', {
                    'thmdef': None,
                    'thms': p[1],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })
    else:
        p[0] = ('note', {
                    'thmdef': p[1],
                    'thms': p[2],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.3
#


def p_interpretation_block(p):
    '''interpretation_block : INTERPRETATION locale_expr proof_prove'''
    p[0] = ('interpretation', {
        'locale_expr': p[2],
        'proof_prove': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.12.2
#

def p_typedecl(p):
    '''typedecl : TYPEDECL typespec
                | TYPEDECL typespec mixfix'''
    p[0] = ('typedecl', {
                'typespec': p[2],
                'mixfix': p[3] if len(p) > 3 else None,
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


def p_type_synonym(p):
    '''type_synonym : TYPE_SYNONYM typespec EQUALS ID
                    | TYPE_SYNONYM typespec EQUALS ID mixfix'''
    p[0] = ('type_synonym', {
                'typespec': p[2],
                'type': p[4],
                'mixfix': p[5] if len(p) > 5 else None,
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.1
#


def p_fix(p):
    '''fix : FIX vars'''
    p[0] = ('fix', p[2])


def p_assume(p):
    '''assume : ASSUME concl prems for_fixes
              | PRESUME concl prems for_fixes'''
    p[0] = (p[1], {
        'concl': p[2] if len(p) == 5 else p[4],
        'prems': p[3] if len(p) == 5 else p[5],
        'for_fixes': p[4] if len(p) == 5 else p[6],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_concl(p):
    '''concl : props
             | NAT COLON props
             | props AND concl
             | NAT COLON props AND concl'''
    if len(p) == 2:
        p[0] = [('concl', {
            'props': p[1],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })]
    elif len(p) == 4:
        if p[2] == ':':
            p[0] = [('concl', {
                'number': p[1],
                'props': p[3],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })]
        else:
            p[0] = [('concl', {
                'props': p[1],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })] + p[3]
    else:
        p[0] = [('concl', {
            'number': p[1],
            'props': p[3],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })] + p[5]


# TODO should be props'_list in first line instead, but don't find definition
# also, should be props_list in second line, but don't find definition
def p_prems(p):
    '''prems : DEFINE vars WHERE prop_list for_fixes
             | IF prop_list DEFINE vars WHERE prop_list for_fixes
             | empty'''
    if len(p) == 2:
        p[0] = ('prems', None)
    elif len(p) == 6:
        p[0] = ('prems', {
            'vars': p[2],
            'props': p[4],
            'for_fixes': p[5],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    else:
        p[0] = ('prems', {
            'conditions': p[2],
            'vars': p[4],
            'props': p[6],
            'for_fixes': p[7],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.2
#


def p_let_block(p):
    '''let_block : LET let_statements'''
    p[0] = p[2]


def p_let_statements(p):
    '''let_statements : let_statement
                      | let_statement AND let_statements'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_let_statement(p):
    '''let_statement : term_list EQUALS term'''
    p[0] = ('let', {
        'terms': p[1],
        'term': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_term_list(p):
    '''term_list : term
                 | term AND term_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.3
#


def p_proof_state(p):
    '''proof_state : NOTE proof_state
                   | NEXT proof_state
                   | LEFT_BRACE proof_state RIGHT_BRACE proof_state
                   | assume proof_state
                   | case proof_state
                   | have proof_prove
                   | show proof_prove
                   | proof proof_state
                   | qed proof_state
                   | qed local_theory
                   | qed theory
                   | qed
                   | terminal_proof_steps
                   | hence proof_prove
                   | thus proof_prove
                   | obtain proof_prove
                   | with proof_chain
                   | fix proof_state'''
    if len(p) == 3:
        p[0] = ('proof_state', {
            'kind': p[1] if p[1] in ['note', 'next'] else None,
            'step': None if p[1] in ['note', 'next'] else p[1],
            'proof': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 4:
        if p[1] == '{' and p[3] == '}':
            p[0] = ('proof_state', {
                'proof_state': p[2],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    else:
        p[0] = p[1]


def p_proof_state_statements(p):
    '''proof_state_statements : proof_state_statement
                              | proof_state_statement AND proof_state_statements'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_proof_state_statement(p):
    '''proof_state_statement : thmdef
                             | thmdef thms'''
    p[0] = ('proof_state', {
        'thmdef': p[1] if len(p) == 2 else None,
        'thms': p[2] if len(p) == 3 else p[1],
    })


def p_proof_chain(p):
    '''proof_chain : have proof_prove
                   | show proof_prove'''
    p[0] = (p[1], p[2])


def p_with(p):
    '''with : WITH thms_list_and_sep'''
    p[0] = ('with', {
        'thms': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


# TODO the first line is adhoc based on AFP, and doesn't match the grammar
def p_local_theory(p):
    '''local_theory : LEMMA thmdecl QUOTED_STRING proof_prove
                    | LEMMA long_statement proof_prove
                    | LEMMA short_statement proof_prove
                    | THEOREM long_statement proof_prove
                    | THEOREM short_statement proof_prove
                    | COROLLARY long_statement proof_prove
                    | COROLLARY short_statement proof_prove
                    | PROPOSITION long_statement proof_prove
                    | PROPOSITION short_statement proof_prove
                    | SCHEMATIC_GOAL long_statement proof_prove
                    | SCHEMATIC_GOAL short_statement proof_prove
        '''
    if len(p) == 5 and p[1] == 'lemma':
        lemma = ('lemma', {
                'name': p[2],
                'statement': p[3],
            })
        p[0] = ('local_theory', {
            'kind': p[1],
            'lemma': lemma,
            'proof': p[4],
            })
    else:
        p[0] = ('local_theory', {
            'kind': p[1],
            'statement': p[2],
            'proof': p[3],
            })


def p_proof_prove(p):
    '''proof_prove : UNFOLDING proof_prove
                   | SHOW stmt cond_stmt
                   | SHOW stmt cond_stmt for_fixes
                   | HENCE stmt cond_stmt
                   | HENCE stmt cond_stmt for_fixes
                   | apply_block proof_prove
                   | apply_block
                   | supply_block proof_prove
                   | supply_block
                   | defer_block proof_prove
                   | defer_block
                   | prefer_block proof_prove
                   | prefer_block
                   | by proof_state
                   | by
                   | using proof_prove
                   | using
                   | with proof_chain
                   | proof proof_state
                   | proof
                   | terminal_proof_steps proof_state
                   | terminal_proof_steps local_theory
                   | terminal_proof_steps theory'''
    p[0] = p[1:]


def p_stmt(p):
    '''stmt : prop_list'''
    p[0] = ('stmt', p[1])


def p_cond_stmt(p):
    '''cond_stmt : empty
                 | IF stmt
                 | WHEN stmt'''
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = ('if', p[2])


def p_short_statement(p):
    '''short_statement : stmt for_fixes
                       | stmt IF stmt for_fixes'''
    p[0] = ('short_statement', {

        'stmt': p[1],
        'if_stmt': p[3] if len(p) == 5 else None,
        'for_fixes': p[4] if len(p) == 5 else p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_long_statement(p):
    '''long_statement : context conclusion
                      | thmdecl context conclusion'''
    p[0] = ('long_statement', {
        'thmdecl': p[1] if len(p) == 3 else None,
        'context': p[1] if len(p) == 2 else p[2],
        'conclusion': p[2] if len(p) == 2 else p[3],
        })


def p_context(p):
    '''context : empty
               | includes
               | context_element_list
               | includes context_element_list'''
    p[0] = ('context', p[1:])


def p_context_element_list(p):
    '''context_element_list : context_elem
                            | context_elem context_element_list'''
    p[0] = [p[1]] + p[2] if len(p) == 3 else [p[1]]


def p_conclusion(p):
    '''conclusion : SHOWS stmt
                  | OBTAINS obtain_clauses'''
    if p[1] == 'shows':
        p[0] = ('conclusion', {
            'shows': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    else:
        p[0] = ('conclusion', {
            'obtains': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_obtain_clauses(p):
    '''obtain_clauses : obtain_clause
                      | obtain_clause AND obtain_clauses'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_obtain_clause(p):
    '''obtain_clause : obtain_case
                     | par_name obtain_case'''
    p[0] = ('obtain_clause', {
        'par_name': p[1] if len(p) == 3 else None,
        'obtain_case': p[1] if len(p) == 2 else p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_obtain_case(p):
    '''obtain_case : obtain_case_statements
                   | vars WHERE obtain_case_statements'''
    p[0] = ('obtain_case', {
        'vars': p[1] if len(p) == 4 else None,
        'obtain_case_statements': p[2] if len(p) == 4 else p[1],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_obtain_case_statements(p):
    '''obtain_case_statements : obtain_case_statement
                              | obtain_case_statement AND obtain_case_statements'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_obtain_case_statement(p):
    '''obtain_case_statement : prop_list
                             | thmdecl prop_list'''
    p[0] = ('obtain_case_statement', {
        'thmdecl': p[1] if len(p) == 3 else None,
        'prop_list': p[2] if len(p) == 2 else p[1],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_using(p):
    '''using : USING thms_list_and_sep'''
    p[0] = ('using', {
        'thms': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_thms_list_and_sep(p):
    '''thms_list_and_sep : thm
                         | thm thms_list_and_sep
                         | thm AND thms_list_and_sep'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = p[1] + p[(len(p) - 1)]


# no rail road diagram
def p_assms(p):
    '''assms : ASSMS'''
    p[0] = ('assms', {
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.4
#

def p_have(p):
    '''have : HAVE stmt cond_stmt for_fixes'''
    p[0] = ('have', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_show(p):
    '''show : SHOW stmt cond_stmt for_fixes'''
    p[0] = ('show', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_hence(p):
    '''hence : HENCE stmt cond_stmt
             | HENCE stmt cond_stmt for_fixes'''
    p[0] = ('hence', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4] if len(p) == 5 else None,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_thus(p):
    '''thus : THUS stmt cond_stmt
            | THUS stmt cond_stmt for_fixes'''
    p[0] = ('thus', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4] if len(p) == 5 else None,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.1
#


def p_method(p):
    '''method : method_name
              | LEFT_PAREN method_name method_args RIGHT_PAREN
              | LEFT_PAREN methods RIGHT_PAREN
              | method_name method_modifier
              | LEFT_PAREN method_name method_args RIGHT_PAREN method_modifier'''
    if len(p) == 2:
        p[0] = ('method', {
            'name': p[1],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 3:
        p[0] = ('method', {
            'name': p[1],
            'modifier': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 4:
        p[0] = ('method', {
            'methods': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 5:
        p[0] = ('method', {
            'name': p[2],
            'args': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    else:
        p[0] = ('method', {
            'name': p[2],
            'args': p[3],
            'modifier': p[5],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_method_modifier(p):
    '''method_modifier : QUESTION_MARK
                       | PLUS
                       | LEFT_BRACKET NAT RIGHT_BRACKET'''
    if len(p) == 2:
        p[0] = ('method_modifier', {
            'modifier': p[1],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    else:
        p[0] = ('method_modifier', {
            'modifier': 'times',
            'nat': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })


# TODO keywords overlap: INDUCT
# TODO this seems to overlap with p_method
def p_methods(p):
    '''methods : method
               | method methods
               | method COMMA methods
               | method SEMICOLON methods
               | method PIPE methods'''
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 3:
        p[0] = ('method', {
            'name': p[1],
            'args': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 4:
        p[0] = ('methods', {
            'method': p[1],
            'sep': p[2],
            'methods': p[3],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 5:
        p[0] = ('methods', {
            'method': ('method', {
                'name': p[1],
                'args': p[2],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                }),
            'sep': p[3],
            'methods': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_goal_spec(p):
    '''goal_spec : LEFT_BRACKET NAT DASH NAT RIGHT_BRACKET
                 | LEFT_BRACKET NAT DASH RIGHT_BRACKET
                 | LEFT_BRACKET NAT RIGHT_BRACKET
                 | LEFT_BRACKET BANG RIGHT_BRACKET'''
    if len(p) == 6:
        p[0] = ('goal_spec', {
            'from': p[2],
            'to': p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 5:
        p[0] = ('goal_spec', {
            'from': p[2],
            'to': None,
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 4:
        p[0] = ('goal_spec', {
            'at': p[2],
            'bang': True,
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.2
#


def p_proof(p):
    '''proof : PROOF method
             | PROOF DASH
             | PROOF'''
    p[0] = ('proof', {
        'method': p[2] if len(p) == 3 else None,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_qed(p):
    '''qed : QED
           | QED method'''
    p[0] = ('qed', {
        'method': p[2] if len(p) == 3 else None,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_by(p):
    '''by : BY method
          | BY method method'''
    if len(p) > 3 and p[3][0] == 'method':
        methods = [p[2], p[3]]
    else:
        methods = [p[2]]

    p[0] = ('by', {
        'methods':  methods,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_terminal_proof_steps(p):
    '''terminal_proof_steps : DOT
                            | DOT DOT
                            | SORRY'''
    p[0] = p[1] if len(p) == 2 else "".join(p[1:])


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.1
#


# TODO complete
def p_case(p):
    '''case : CASE ID
            | CASE LEFT_PAREN name_underscore_list RIGHT_PAREN'''
    p[0] = ('case', {
        'names': [p[2]] if len(p) == 3 else p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_name_underscore_list(p):
    '''name_underscore_list : ID
                            | UNDERSCORE
                            | ID name_underscore_list
                            | UNDERSCORE name_underscore_list'''
    p[0] = [p[1]] + p[2] if len(p) == 3 else [p[1]]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.2
#


def p_induct_block(p):
    '''induct_block : INDUCT no_simp_block definsts_list_block arbitary_block taking rule_block
                    | INDUCTION no_simp_block definsts_list_block arbitary_block taking rule_block'''
    p[0] = (p[1], {
        'no_simp': p[2],
        'definsts_list': p[3],
        'arbitary': p[4],
        'taking': p[5],
        'rule': p[6],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_no_simp_block(p):
    '''no_simp_block : empty
                     | LEFT_PAREN NO_SIMP RIGHT_PAREN'''
    p[0] = len(p) == 4


def p_definsts_list_block(p):
    '''definsts_list_block : empty
                           | definst AND definsts_list_block'''
    p[0] = [] if len(p) == 2 else [p[1]] + p[3]


def p_definst(p):
    '''definst : ID EQUALS EQUALS term
               | ID EQUIV term
               | LEFT_PAREN term RIGHT_PAREN
               | inst'''
    if len(p) == 2:
        p[0] = p[1]
    elif p[1] == '(':
        p[0] = p[2]
    else:
        p[0] = ('definst', {
            'name': p[1],
            'comparison': "equiv" if len(p) == 4 else "equals",
            'term': p[len(p)-1],
            })


def p_arbitary_block(p):
    '''arbitary_block : empty
                      | arbitrary'''
    p[0] = p[1]


def p_arbitrary(p):
    '''arbitrary : ARBITRARY COLON term_list_and'''
    p[0] = ('arbitrary', {
        'terms': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_term_list_and(p):
    '''term_list_and : term
                     | term AND term_list_and'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_taking(p):
    '''taking : empty
              | TAKING COLON insts'''
    if len(p) == 2:
        p[0] = None
    else:
        p[0] = ('taking', {
            'insts': p[3],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_rule_block(p):
    '''rule_block : empty
                  | rule'''
    p[0] = p[1]


def p_coinduct_block(p):
    '''coinduct_block : COINDUCT insts taking
                      | COINDUCT insts taking rule'''
    p[0] = ('coinduct', {
            'insts': p[2],
            'taking': p[3],
            'rule': p[4] if len(p) > 4 else None,
            })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.6
#

# TODO complete
def p_obtain(p):
    '''obtain : OBTAIN vars WHERE concl prems for_fixes
              | OBTAIN vars WHERE par_name concl prems for_fixes
              | OBTAIN concl prems for_fixes
              | OBTAIN par_name concl prems for_fixes'''
    if len(p) == 4:
        p[0] = ('obtain', {
            'concl': p[2],
            'prems': p[3],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 5:
        p[0] = ('obtain', {
            'par_name': p[2] if p[2][0] == 'par_name' else None,
            'concl': p[3] if p[2][0] == 'par_name' else p[2],
            'prems': p[4] if p[2][0] == 'par_name' else p[3],
            'for_fixes': None if p[2][0] == 'par_name' else p[4],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 6:
        p[0] = ('obtain', {
            'par_name': p[2] if p[2][0] == 'par_name' else None,
            'vars': None if p[2][0] == 'par_name' else p[2],
            'concl': p[4] if p[3] == 'where' else p[3],
            'prems': p[5] if p[3] == 'where' else p[4],
            'for_fixes': None if p[3] == 'where' else p[5],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    elif len(p) == 7:
        p[0] = ('obtain', {
            'par_name': p[4] if p[4][0] == 'par_name' else None,
            'vars': p[2],
            'concl': p[5] if p[4][0] == 'par_name' else p[4],
            'prems': p[6] if p[4][0] == 'par_name' else p[5],
            'for_fixes': None if p[4][0] == 'par_name' else p[6],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })
    else:
        p[0] = ('obtain', {
            'vars': p[2],
            'par_name': p[4],
            'concl': p[5],
            'prems': p[6],
            'for_fixes': p[7],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 7.1
#


def p_apply_block(p):
    '''apply_block : APPLY method
                   | APPLY_END method'''
    p[0] = ('apply', {
        'end': p[1] == 'apply_end',
        'method': p[2],
        })


def p_supply_block(p):
    '''supply_block : SUPPLY proof_state_statements'''
    p[0] = ('supply', {
        'statements': p[2],
        })


def p_defer_block(p):
    '''defer_block : DEFER
                   | DEFER NAT'''
    p[0] = ('defer', {
        'number': p[2] if len(p) > 2 else None,
        })


def p_prefer_block(p):
    '''prefer_block : PREFER NAT'''
    p[0] = ('prefer', {
        'number': p[2],
        })


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.2
#


def p_mixfix(p):
    '''mixfix : LEFT_PAREN template RIGHT_PAREN
              | LEFT_PAREN template prios RIGHT_PAREN
              | LEFT_PAREN template NAT RIGHT_PAREN
              | LEFT_PAREN template prios NAT RIGHT_PAREN
              | LEFT_PAREN INFIX template NAT RIGHT_PAREN
              | LEFT_PAREN INFIXL template NAT RIGHT_PAREN
              | LEFT_PAREN INFIXR template NAT RIGHT_PAREN
              | BINDER template NAT RIGHT_PAREN
              | BINDER template prio NAT RIGHT_PAREN
              | STRUCTURE'''
    line = p.lineno(1)
    column = get_column(source, p.lexpos(1)) if source else -1
    if len(p) == 1:
        p[0] = ('mixfix', {
                    'type': p[1],
                    'line': line,
                    'column': column,
                    })
    elif p[2] in ['infix', 'infixl', 'infixr']:
        p[0] = ('mixfix', {
                    'type': p[2],
                    'template': p[3],
                    'nat': p[4],
                    'line': line,
                    'column': column,
                    })
    elif p[1] == 'binder':
        p[0] = ('mixfix', {
                    'type': p[1],
                    'template': p[2],
                    'prio': p[3] if len(p) > 4 else None,
                    'nat': p[4] if len(p) > 4 else p[3],
                    'line': line,
                    'column': column,
                    })
    elif p[1] == '(':
        if len(p) == 4 and isinstance(p[3], int):
            nat = p[3]
        elif len(p) > 4:
            nat = p[4]
        else:
            nat = None

        if len(p) >= 5 and isinstance(p[3], list):
            prios = p[3]
        else:
            prios = None

        p[0] = ('mixfix', {
            'nat': nat,
            'prios': prios,
            'type': 'template',
            'template': p[2],
            'line': line,
            'column': column,
            })


def p_template(p):
    '''template : QUOTED_STRING
                | CARTOUCHE'''
    p[0] = p[1]


def p_prios(p):
    '''prios : LEFT_BRACKET nat_list RIGHT_BRACKET'''
    p[0] = p[2]


def p_prio(p):
    '''prio : LEFT_BRACKET NAT RIGHT_BRACKET'''
    p[0] = p[2]


def p_nat_list(p):
    '''nat_list : NAT
                | NAT COMMA nat_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.3
#


def p_notation_block(p):
    '''notation_block : NOTATION notation_list
                      | NOTATION mode notation_list'''
    p[0] = ('notations', {
        'mode': p[2] if len(p) == 3 else None,
        'notation_list': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_notation_list(p):
    '''notation_list : notation
                     | notation AND notation_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_notation(p):
    '''notation : ID mixfix'''
    p[0] = ('notation', {
        'name': p[1],
        'mixfix': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })

# TODO
def p_mode(p):
    '''mode : ID'''
    p[0] = p[1]

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2
#

def p_primrec_block(p):
    '''primrec_block : PRIMREC specification'''
    p[0] = ('primrec', p[2])


def p_fun_block(p):
    '''fun_block : FUN specification
                 | FUNCTION specification
                 | FUN opts specification
                 | FUNCTION opts specification'''
    p[0] = ('fun', {
        'specification': p[2] if len(p) == 3 else p[3],
        'opts': p[2] if len(p) == 4 else None,
        })


def p_opts(p):
    '''opts : LEFT_PAREN opt_list RIGHT_PAREN'''
    p[0] = ('opts', p[2])


def p_opt_list(p):
    '''opt_list : sequential
                | domintros
                | sequential COMMA opt_list
                | domintros COMMA opt_list'''

    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


# TODO: not spec'ed
def p_sequential(p):
    '''sequential : ID
                  | QUOTED_STRING'''
    p[0] = p[1]


# TODO: not spec'ed
def p_domintros(p):
    '''domintros : ID
                 | QUOTED_STRING'''
    p[0] = p[1]


#
# Should be lexer rules, but overlap
#


# symbol = r'[!#$%&*+\-/<=>?@^_`|~]'
def p_symbol(p):
    '''symbol : BANG
              | STAR
              | BACKSLASH
              | LT
              | HAT
              | GT
              | PLUS'''
    p[0] = p[1]

# t_SYM_FLOAT = r'(\d+(\.\d+)?|\.\d+)'
# t_DIGIT = r'[0-9]'
# t_QUASILETTER = r'[a-zA-Z0-9._]'


def p_empty(_):
    '''empty :'''
    pass


def p_error(p):

    print("\nParser state stack:")
    for i, state in enumerate(_parser.statestack):
        print(f"  {i}: State {state}")

        # Retrieve the possible actions from the `lr_action` table
        state_actions = _parser.action[state]
        for symbol, action in state_actions.items():
            if action > 0:
                # Shift action (useful for debugging symbol expectations)
                print(f"      Shift on {symbol} -> Go to state {action}")
            elif action < 0:
                # Reduce action, find corresponding production
                production_index = -action
                production = _parser.productions[production_index]
                print(f"      Reduce by rule: {production}")
            else:
                # Action 0 means an error or default action, usually no specific rule
                print("      No specific rule (Error/Default action)")

    print("\nLast few productions leading to error:")
    lookahead = 10
    for i, prod in enumerate(_parser.productions[-lookahead:]):
        print(f"  {i+1-lookahead}: {prod}")

    print("\nSymbol stack track:")
    for i, sym in enumerate(_parser.symstack):
        print(f"  {i}: Symbol {sym}")

    print("")

    if p:
        value = p.value
        column = get_column(source, p.lexpos) if source else -1
        lineno = p.lineno
    else:
        value = "NONE"
        column = -1
        lineno = -1
    raise ParsingError(f"Syntax error at '{value}'",
                       line=lineno,
                       column=column,
                       token=value)


# Define precedence and associativity (optional for Isabelle)
precedence = ()


# Build the parser
_parser = yacc.yacc(debug=True)


source = None


def parse(input):
    global source
    source = input
    reset_lexer(lexer)
    return _parser.parse(input)
