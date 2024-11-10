import ply.yacc as yacc
import logging

from .error import ParsingError
from .thy_lexer import lexer, reset_lexer, get_column, tokens

__all__ = ['tokens']


logger = logging.getLogger(__name__)


def p_theory_file(p):
    '''theory_file : theory
                   | section_block theory_file
                   | text_block theory_file'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_theory(p):
    '''theory : THEORY ID imports_opt BEGIN content END'''
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
    '''import_list : ID import_list
                   | QUOTED_STRING import_list
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


def p_statement(p):
    '''statement : axiomatization_block
                 | fun_block
                 | interpretation_block
                 | lemma_block
                 | locale_block
                 | method_block
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
    '''method_name : ID'''
    p[0] = p[1]


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
    '''single_instruction : ID
                          | ID method_args
                          | LEFT_PAREN ID method_args RIGHT_PAREN
                          | LEFT_PAREN ID method_args RIGHT_PAREN instruction_modifier'''
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
    '''method_args : ID COLON method_arg method_args
                   | method_arg method_args
                   | empty'''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    elif len(p) == 5:
        p[0] = [p[1], p[2], p[3]] + p[4]
    else:
        p[0] = []


def p_method_arg(p):
    '''method_arg : ID
                  | ID LEFT_PAREN NAT RIGHT_PAREN
                  | ID DOT ID
                  | ID DOT ID LEFT_PAREN NAT RIGHT_PAREN
                  | QUOTED_STRING'''
    p[0] = "".join(p[1:])


def p_lemma_block(p):
    '''lemma_block : LEMMA ID COLON assumes_block shows_clause lemma_proof_block'''
    p[0] = ('lemma', {
        'name': p[2],
        'assumes': p[4],
        'shows': p[5],
        'proof': p[6],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })


def p_lemma_proof_block(p):
    '''lemma_proof_block : PROOF apply_block
                         | apply_block
                         | empty'''
    if len(p) == 3:
        p[0] = ('proof', p[2])
    elif len(p) == 2:
        p[0] = ('proof', p[1])
    else:
        p[0] = ('proof',)


def p_assumes_block(p):
    '''assumes_block : ASSUMES assumptions_list'''
    p[0] = p[2]


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


def p_shows_clause(p):
    '''shows_clause : SHOWS QUOTED_STRING'''
    p[0] = ('shows', p[2])


def p_apply_block(p):
    '''apply_block : single_apply apply_block
                   | subgoal apply_block
                   | empty'''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    else:
        p[0] = []


def p_single_apply(p):
    '''single_apply : APPLY instruction
                    | APPLY LEFT_PAREN instruction RIGHT_PAREN
                    | USING using_block APPLY DASH
                    | USING using_block APPLY instruction
                    | USING using_block APPLY LEFT_PAREN instruction RIGHT_PAREN
                    | BY instruction
                    | BY LEFT_PAREN instruction RIGHT_PAREN
                    | USING using_block BY instruction
                    | USING using_block BY LEFT_PAREN instruction RIGHT_PAREN
                    | DONE
                    | SORRY
                    '''
    if len(p) == 2:
        if p[1] in ['done', 'sorry']:
            p[0] = ('apply', {
                'type': p[1],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })
        else:
            p[0] = p[1]
    elif len(p) == 3:
        type = p[1]
        p[0] = ('apply', {
            'type': type,
            'instruction': p[2],
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
        })
    elif len(p) == 5:
        if p[1] == 'using':
            p[0] = ('apply', {
                'type': p[3],
                'using': p[2],
                'instruction': p[4],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })
        elif p[2] == '(' and p[4] == ')':
            p[0] = ('apply', {
                'type': p[1],
                'instruction': p[3],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })
        else:
            raise SyntaxError
    elif len(p) == 7:
        if p[4] == '(' and p[6] == ')':
            p[0] = ('apply', {
                'type': p[3],
                'using': p[2],
                'instruction': p[5],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })
        else:
            raise SyntaxError
    else:
        raise SyntaxError


def p_using_block(p):
    '''using_block : ASSMS using_block
                   | ASSMS LEFT_PAREN NAT RIGHT_PAREN using_block
                   | ASSMS LEFT_PAREN NAT COMMA NAT RIGHT_PAREN using_block
                   | ASSMS LEFT_PAREN NAT DASH NAT RIGHT_PAREN using_block
                   | empty'''
    if len(p) == 2:
        p[0] = []
    elif len(p) > 2:
        head = "".join(p[1:-1])
        p[0] = [head] + p[len(p)-1]


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
    '''vars : var
            | var AND vars'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_var(p):
    '''var : names
           | ID COLON COLON ID
           | GREEK COLON COLON ID
           | ID COLON COLON QUOTED_STRING
           | GREEK COLON COLON QUOTED_STRING
           | names COLON COLON ID
           | names COLON COLON QUOTED_STRING
           | ID mixfix
           | ID COLON COLON ID mixfix
           | GREEK COLON COLON ID mixfix
           | ID COLON COLON QUOTED_STRING mixfix
           | GREEK COLON COLON QUOTED_STRING mixfix'''
    if len(p) == 2:
        names = p[1]
    else:
        if isinstance(p[1], list):
            names = p[1]
        else:
            names = [p[1]]
    p[0] = ('var', {
                'names': names,
                'type': p[4],
                'mixfix': p[5] if len(p) > 5 else None,
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
                })

# def p_props(p):
#     '''props : prop_list
#              | thmdecl prop_list'''
#     p[0] = ('props', {
#                 'thmdecl': p[1] if len(p) == 3 else None,
#                 'props': p[1] if len(p) == 2 else p[2],
#                 'line': p.lineno(1),
#                 'column': get_column(source, p.lexpos(1)) if source else -1,
#                 })
#
#
# def p_prop_list(p):
#     '''prop_list : prop
#                  | prop prop_list
#                  | prop prop_pat prop_list'''
#     p[0] = [(p[1], p[2] if len(p) > 2 else None)] + p[3] if len(p) > 2 else [p[1]]


def p_names(p):
    '''names : ID
             | ID AND names'''
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
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.9
#


def p_thmdecl(p):
    '''thmdecl : thmbind COLON'''
    p[0] = ('thmdecl', p[1])


def p_thmdef(p):
    '''thmdef : thmbind EQ'''
    p[0] = ('thmdef', p[1])


def p_thm(p):
    '''thm : ID attributes
           | ID
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
    '''for_fixes : FOR vars'''
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
    '''prop_list : ID
                 | ID prop_list
                 | ID AND prop_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    elif len(p) == 3:
        p[0] = [p[1]] + p[2]
    else:
        p[0] = [p[1]] + p[3]


def p_specification(p):
    '''specification : vars WHERE multi_specs'''
    p[0] = ('specification', {
        'vars': p[1],
        'multi_specs': p[3],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.3
#

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
    '''locale_expr : instance_list
                   | instance_list for_fixes'''
    p[0] = ('locale_expr', {
        'instances': p[1],
        'for_fixes': p[2] if len(p) == 3 else [],
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
                 | DOT
                 | ID
                 | QUOTED_STRING
                 | GREEK
                 | UNDERSCORE pos_insts
                 | DOT pos_insts
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
    '''interpretation_block : INTERPRETATION locale_expr'''
    p[0] = ('interpretation', p[2])


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
    if len(p) == 1:
        p[0] = ('mixfix', {
                    'type': p[1],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })
    elif p[2] in ['infix', 'infixl', 'infixr']:
        p[0] = ('mixfix', {
                    'type': p[2],
                    'template': p[3],
                    'nat': p[4],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
                    })
    elif p[1] == 'binder':
        p[0] = ('mixfix', {
                    'type': p[1],
                    'template': p[2],
                    'prio': p[3] if len(p) > 4 else None,
                    'nat': p[4] if len(p) > 4 else p[3],
                    'line': p.lineno(1),
                    'column': get_column(source, p.lexpos(1)) if source else -1,
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
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
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
# Docs
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

    # Accessing the parser state stack for trace
    print("Parser rule stack trace:")
    for i, (sym, state) in enumerate(zip(_parser.symstack, _parser.statestack)):
        print(f"  Step {i}: State {state} -> Symbol {sym}")

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
