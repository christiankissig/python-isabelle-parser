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
                   | doc_block theory_file
                   | marker theory_file
                   '''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_theory_block(p):
    '''theory_block : THEORY name imports_opt BEGIN theory END'''
    global source
    imports = p[3]
    p[0] = (
        'theory',
        {
            'name': p[2],
            'imports': imports[1],
            'content': p[5],
        }
    )
    add_position(p)


def p_imports_opt(p):
    '''imports_opt : IMPORTS import_list
                   | empty'''
    p[0] = ('imports', p[2]) if len(p) > 2 else ('imports', [])


def p_import_list(p):
    '''import_list : QUOTED_STRING import_list
                   | comment_block import_list
                   | ID import_list
                   | ID DOT ID import_list
                   | ID DOT ID
                   | ID
                   | QUOTED_STRING
                   | comment_block
                   '''
    if len(p) == 2:
        p[0] = [p[1]]
    elif p[2] == '.':
        p[0] = ["".join(p[1:3])]
        if len(p) > 4:
            p[0] += p[4]
    else:
        p[0] = [p[1]] + p[2]


def p_theory(p):
    '''theory : goal proof_prove
              | statement theory
              | class_instance proof_prove
              | empty
              '''
    if len(p) == 3:
        p[0] = [p[1]] + p[2]
    else:
        p[0] = []


def p_statement(p):
    '''statement : abbreviation
                 | axiomatization_block
                 | comment_block
                 | consts
                 | context
                 | datatype
                 | declaration
                 | declare
                 | definition
                 | doc_block
                 | export_code
                 | fun_block
                 | hide_declarations
                 | inductive
                 | instantiation
                 | interpretation_block
                 | lemmas
                 | locale_block
                 | marker
                 | method_block
                 | ml
                 | notation_block
                 | partial_function
                 | primrec
                 | record
                 | syntax
                 | translations
                 | type_synonym
                 | typedecl
                 '''
    p[0] = p[1]


def p_method_block(p):
    '''method_block : METHOD name EQUALS instruction'''
    p[0] = ('method', {
        'name': p[2],
        'instruction': p[4],
    })
    add_position(p)


def p_instruction(p):
    '''instruction : single_instruction
                   | single_instruction instruction_modifier
                   | single_instruction instruction_modifier COMMA instruction
                   | single_instruction SEMICOLON instruction
                   | single_instruction COMMA instruction
                   | LEFT_PAREN instruction RIGHT_PAREN
                   | LEFT_PAREN instruction RIGHT_PAREN instruction_modifier'''
    p[0] = ('instruction', *p[1:])
    add_position(p)


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
                })
    elif len(p) == 3:
        p[0] = ('single_instruction',
                {
                    'method': p[1],
                    'args': p[2],
                })
    elif len(p) == 5:
        p[0] = ('single_instruction',
                {
                    'method': p[2],
                    'args': p[3],
                })
    elif len(p) == 6:
        p[0] = ('single_instruction',
                {
                    'method': p[2],
                    'args': p[3],
                    'modifier': p[5],
                })
    add_position(p)


def p_var_list_nosep(p):
    '''var_list_nosep : var var_list_nosep
                      | var'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_assumptions_list(p):
    '''assumptions_list : assumption AND assumptions_list
                        | assumption'''
    if len(p) > 2:
        p[0] = [p[1]] + p[3]
    else:
        p[0] = [p[1]]


def p_assumption(p):
    '''assumption : QUOTED_STRING
                  | NAT COLON QUOTED_STRING
                  | ID COLON QUOTED_STRING'''
    p[0] = ('assumption',
            {
                'id': p[1] if len(p) > 2 else None,
                'text': p[1] if len(p) == 2 else p[3],
                'line': p.lineno(1),
                'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_subgoal(p):
    '''subgoal : SUBGOAL name COLON
               | SUBGOAL
               '''
    p[0] = ('subgoal', {
        'name': p[2] if len(p) > 2 else None,
    })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.1
#


def p_name(p):
    '''name : ID
            | CASE
            | CASES
            | GREEK
            | ID DOT
            | ID DOT CASES
            | ID DOT name
            | ID SUBSCRIPT NAT
            | ID SUBSCRIPT name
            | IN
            | INDUCT
            | NAT
            | PRED
            | QUOTED_STRING
            | STAR
            | STAR STAR
            | SYM_IDENT
            | WHERE
            '''
    p[0] = ''.join(p[1:])


def p_par_name(p):
    '''par_name : LEFT_PAREN name RIGHT_PAREN'''
    p[0] = ('par_name', {
        'name': p[2],
    })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.3
#


def p_embedded(p):
    '''embedded : ID
                | QUOTED_STRING
                | CARTOUCHE
                | NAT
                | GREEK
                | TRUE
                | FALSE
                | VAR_CASE
                | VAR_THESIS
                | TYPE_IDENT
                | SYM_IDENT
                '''
    p[0] = p[1]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.7
#


def p_type(p):
    '''type : embedded'''
    p[0] = ('type', p[1])


def p_term(p):
    '''term : QUOTED_STRING
            | GREEK
            | ID
            | TERM_VAR
            | SYM_IDENT'''
    term = p[1]
    p[0] = ('term', term)


def p_named_prop_list_and_sep(p):
    '''named_prop_list_and_sep : named_prop AND named_prop_list_and_sep
                               | named_prop'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_named_prop(p):
    '''named_prop : prop
                  | prop_list
                  | ID COLON prop
                  | NAT COLON prop
                  | STAR COLON prop
                  | STAR STAR COLON prop
                  | STAR STAR STAR COLON prop'''
    if p[len(p)-2] == ':':
        id = "".join(p[1:len(p)-2])
    else:
        id = p[1]
    p[0] = ('named_prop', {
            'id': id,
            'prop': p[len(p)-1],
            })
    add_position(p)


def p_prop(p):
    '''prop : embedded'''
    p[0] = ('prop', {
        'prop': p[len(p)-1],
        })
    add_position(p)


def p_inst(p):
    '''inst : UNDERSCORE
            | term'''
    p[0] = ('inst', p[1])


def p_insts(p):
    '''insts : inst insts
             | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = [p[1]] + p[2]


def p_typespec(p):
    '''typespec : ID
                | typeargs ID'''
    p[0] = ('typespec', {
                'typeargs': p[1] if len(p) == 3 else [],
                'name': p[2] if len(p) == 3 else p[1],
                })
    add_position(p)


def p_typearg(p):
    '''typearg : ID
               | TYPE_IDENT
               | ID COLONCOLON ID'''
    p[0] = ('typearg', {
                'name': p[1],
                'sort': p[4] if len(p) > 2 else None,
                })
    add_position(p)


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


def p_typeargs_sorts(p):
    '''typeargs_sorts : empty
                      | type_ident_with_sort
                      | LEFT_PAREN type_ident_with_sort_list RIGHT_PAREN'''
    if len(p) == 2 and p[1]:
        type_idents = [p[1]]
    elif len(p) == 4:
        type_idents = p[2]
    else:
        type_idents = None
    p[0] = ('typeargs_sorts',
            {
                'type_idents': type_idents,
            })
    add_position(p)


def p_type_ident_with_sort(p):
    '''type_ident_with_sort : TYPE_IDENT COLONCOLON sort
                            | TYPE_IDENT'''
    p[0] = ('type_ident_with_sort', {
            'ident': p[1],
            'sort': p[4] if len(p) == 5 else None,
            })
    add_position(p)


def p_type_ident_with_sort_list(p):
    '''type_ident_with_sort_list : type_ident_with_sort
                                 | type_ident_with_sort COMMA type_ident_with_sort_list'''
    p[0] = [p[1]] if len(p) == 2 else [p[1]] + p[3]


def p_typespec_sorts(p):
    '''typespec_sorts : typeargs_sorts name'''
    p[0] = ('typespec_sorts', {
        'typeargs_sorts': p[1],
        'name': p[2],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.6
#


def p_sort(p):
    '''sort : ID'''
    p[0] = ('sort', {'sort': p[1]})
    add_position(p)


def p_sort_list_comma_sep(p):
    '''sort_list_comma_sep : sort
                           | sort COMMA sort_list_comma_sep'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_arity(p):
    '''arity : LEFT_PAREN sort_list_comma_sep RIGHT_PAREN sort
             | sort'''
    p[0] = ('arity', {
        'sorts': p[2] if len(p) == 5 else [],
        'sort': p[4] if len(p) == 5 else p[1],
        })
    add_position(p)


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
    '''var : name COLONCOLON type
           | names COLONCOLON type
           | name COLONCOLON type mixfix
           | name mixfix
           | names
           | name'''
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
                })
    add_position(p)


def p_props(p):
    '''props : prop_list_with_pat
             | thmdecl prop_list_with_pat'''
    p[0] = ('props', {
                'thmdecl': p[1] if len(p) == 3 else None,
                'props': p[1] if len(p) == 2 else p[2],
                })
    add_position(p)


def p_prop_list_with_pat(p):
    '''prop_list_with_pat : prop prop_pat prop_list_with_pat
                          | prop AND prop_list_with_pat
                          | prop prop_list_with_pat
                          | prop prop_pat
                          | prop'''
    prop = p[1]
    prop_pat = None
    props = []

    if len(p) > 2 and isinstance(p[2], list):
        props = p[2]
    elif len(p) > 2 and p[2][0] == 'prop_pat':
        prop_pat = p[2]
    elif len(p) > 3:
        props = p[len(p)-1]

    prop_with_pat = ('prop_with_pat', {
        'prop': prop,
        'prop_pat': prop_pat,
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
    })
    p[0] = [prop_with_pat] + props


def p_names(p):
    '''names : ID AND names
             | ID'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_name_list(p):
    '''name_list : name
                 | name name_list'''
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


def p_method_arg_atom(p):
    '''method_arg_atom : name
                       | NAT
                       | CARTOUCHE
                       | ASSMS
                       | STAR
                       | name COLON
                       | ARBITRARY COLON
                       | RULE COLON
                       | ID BANG COLON
                       | name DOT CASES
                       | name DOT INDUCT
                       | name SUBSCRIPT NAT
                       | name LEFT_PAREN NAT RIGHT_PAREN
                       | name LEFT_PAREN NAT COMMA NAT RIGHT_PAREN COLON
                       | name EQUALS name
                       | cases
                       '''
    p[0] = "".join(p[1:])


# TODO arbitary and rule should be instances of rule
def p_method_arg(p):
    '''method_arg : method_arg_atom
                  | LEFT_PAREN method_args RIGHT_PAREN
                  | LEFT_BRACKET method_args RIGHT_BRACKET
                  '''
    p[0] = ('method_arg', {
        'atom': p[1] if len(p) == 2 else None,
        'args': p[2] if len(p) == 4 else None,
        })
    add_position(p)


def p_method_args(p):
    '''method_args : method_arg method_args
                   | method_arg AND method_args
                   | method_arg COMMA method_args
                   | method_arg
                   | empty'''
    if len(p) == 2 and not p[1]:
        p[0] = []
        return
    arg = p[1]
    args = p[len(p)-1] if len(p) > 2 else []
    p[0] = [arg] + args


def p_attributes(p):
    '''attributes : LEFT_BRACKET name_insts_attributes_list RIGHT_BRACKET'''
    p[0] = ('attributes', {
        'attributes': p[2],
        })
    add_position(p)


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
        p[0] = [p[1]] + p[len(p) - 1]


def p_name_insts_attributes_list(p):
    '''name_insts_attributes_list : empty
                                  | attribute
                                  | attribute COMMA name_insts_attributes_list
                                  | name_insts COMMA name_insts_attributes_list
                                  '''
    if len(p) == 2:
        if p[1] is None:
            p[0] = []
        else:
            p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[len(p) - 1]


# TODO [OF assms(1)] should be handled separately
def p_attribute(p):
    '''attribute : name args
                 | name QUESTION_MARK
                 | name BANG
                 | name EQUALS ID
                 | ID ASSMS LEFT_PAREN NAT RIGHT_PAREN
                 | folded
                 | NAT'''
    name = None
    args = None
    if len(p) > 2:
        if isinstance(p[2], list):
            args = p[2]
        else:
            name = "".join(p[1:])
    else:
        name = p[1]

    p[0] = ('attribute', {
        'name': name,
        'args': args,
        })
    add_position(p)


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
           | CARTOUCHE
           | FALSE
           | FOR
           | GREEK
           | ID SUBSCRIPT ID
           | INFINITY
           | LEFT_BRACKET args RIGHT_BRACKET
           | LEFT_PAREN args RIGHT_PAREN
           | NAT
           | QUOTED_STRING
           | SYM_IDENT
           | TRUE
           '''
    value = None
    args = None
    if len(p) > 2 and isinstance(p[2], list):
        args = p[2]
    else:
        value = ''.join(p[1:])

    p[0] = ('arg', {
            'value': value,
            'args': args,
            'line': p.lineno(1),
            'column': get_column(source, p.lexpos(1)) if source else -1,
            })


def p_thmdecl(p):
    '''thmdecl : thmbind COLON'''
    p[0] = ('thmdecl', p[1])


def p_thmdef(p):
    '''thmdef : thmbind EQUALS'''
    p[0] = ('thmdef', p[1])


def p_thm(p):
    '''thm : NAT
           | ASSMS EQUALS CARTOUCHE
           | CARTOUCHE
           | FALSE
           | ID EQUALS FALSE
           | ID EQUALS ID
           | ID EQUALS ID DOT ID attributes
           | ID EQUALS NAT attributes
           | LEFT_BRACKET attributes RIGHT_BRACKET
           | NAT EQUALS ID
           | NAT attributes
           | STAR
           | SYM_IDENT
           | TRUE
           | assms
           | assms attributes
           | assms selection
           | name
           | name attributes
           | name selection
           | name selection attributes
           '''
    attributes = None
    selection = None
    assms = None
    name = None

    tail_offset = 0
    if isinstance(p[len(p)-1], list):
        attributes = p[len(p)-1]
        tail_offset += 1
    if p[-1-tail_offset][0] == 'selection':
        selection = p[-1-tail_offset]
        tail_offset += 1
    if p[1] == '[' and p[3] == ']':
        attributes = p[2]
    if p[1][0] == 'assms':
        assms = p[1]
    else:
        name = ''.join([s
                        for s in p[1:len(p)-tail_offset]
                        if isinstance(s, str)])

    p[0] = ('thm', {
        'name': name,
        'assms': assms,
        'attributes': attributes,
        'selection': selection,
    })
    add_position(p)


def p_thms(p):
    '''thms : thm
            | assms
            | thm thms'''
    p[0] = [p[1]] + p[2] if len(p) == 3 else [p[1]]


def p_thmbind(p):
    '''thmbind : name attributes
               | name
               | attributes'''
    name = None
    attributes = None
    if p[1][0] == 'attributes':
        attributes = p[1]
    else:
        name = p[1]
    if len(p) > 2 and p[2][0] == 'attributes':
        attributes = p[2]

    p[0] = ('thmbind', {
        'name': name,
        'attributes': attributes,
        })
    add_position(p)


def p_selection(p):
    '''selection : LEFT_PAREN selection_list RIGHT_PAREN'''
    p[0] = ('selection', {
        'selection': p[2],
        'line': p.lineno(1),
        'column': get_column(source, p.lexpos(1)) if source else -1,
        })


def p_selection_list(p):
    '''selection_list : selection_item
                      | selection_item COMMA selection_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_selection_item(p):
    '''selection_item : NAT
                      | NAT DASH
                      | NAT DASH NAT'''
    if len(p) == 2:
        p[0] = ('point', {'at': p[1]})
    elif len(p) == 3:
        p[0] = ('range', {'from': p[1]})
    else:
        p[0] = ('range', {'from': p[1], 'to': p[3]})


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
        })
    elif len(p) == 4:
        p[0] = ('structured_spec', {
            'thmdecl': None,
            'prop': p[1],
            'spec_prems': p[2],
            'for_fixes': p[3],
        })
    else:
        p[0] = ('structured_spec', {
            'thmdecl': p[1],
            'prop': p[2],
            'spec_prems': p[3],
            'for_fixes': p[4],
        })
    add_position(p)


def p_spec_prems(p):
    '''spec_prems : IF prop_list
                  | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = ('if', p[2])


def p_prop_list(p):
    '''prop_list : prop
                 | prop AND prop_list
                 | prop prop_list'''
    p[0] = [p[1]] + p[len(p)-1] if len(p) > 2 else [p[1]]


def p_specification(p):
    '''specification : vars WHERE multi_specs
                     | vars WHERE comment_block multi_specs
                     | vars comment_block WHERE multi_specs'''
    comment = None
    if len(p) > 2 and p[2][0] == 'comment':
        comment = p[2]
    elif len(p) > 3 and p[3][0] == 'comment':
        comment = p[3]
    p[0] = ('specification', {
        'vars': p[1],
        'multi_specs': p[len(p)-1],
        'comment': comment,
        })
    add_position(p)


# TODO p75
def p_antiquotation_body(p):
    '''antiquotation_body : ID'''
    p[0] = ('antiquotation_body', {
        'type': p[1],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.1
#


def p_doc_block(p):
    '''doc_block :  CHAPTER QUOTED_STRING
                 |  CHAPTER CARTOUCHE
                 |  SECTION QUOTED_STRING
                 |  SECTION CARTOUCHE
                 |  SUBSECTION QUOTED_STRING
                 |  SUBSECTION CARTOUCHE
                 |  SUBSUBSECTION QUOTED_STRING
                 |  SUBSUBSECTION CARTOUCHE
                 |  PARAGRAPH QUOTED_STRING
                 |  PARAGRAPH CARTOUCHE
                 |  TEXT QUOTED_STRING
                 |  TEXT CARTOUCHE
                 |  COMMENT_CARTOUCHE QUOTED_STRING
                 |  COMMENT_CARTOUCHE CARTOUCHE

    '''
    p[0] = (p[1], {'text': p[2]})
    add_position(p)


def p_comment_block(p):
    '''comment_block : COMMENT_CARTOUCHE CARTOUCHE'''
    p[0] = ('comment', {'comment': p[2]})
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.2
#


def p_antiquotation(p):
    '''antiquotation : AT LEFT_BRACE antiquotation_body RIGHT_BRACE
                     | SLASH LT HAT ID GT CARTOUCHE
                     | CARTOUCHE'''
    p[0] = ('antiquotation', {
        'body': p[3] if len(p) == 5 else "".join(p[1:]),
    })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.4
#


def p_marker(p):
    '''marker : MARKER CARTOUCHE'''
    p[0] = ('marker', {
        'marker': p[2],
        })
    add_position(p)


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
    '''rule : TYPE COLON name_list
            | PRED COLON name_list
            | SET COLON name_list
            | RULE COLON thms'''
    if len(p) == 2:
        p[0] = ('rule', {
            'name': None,
            'body': p[1],
        })
    elif len(p) == 3:
        p[0] = ('rule', {
            'name': p[1],
            'body': p[2],
        })
    add_position(p)


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
    })
    add_position(p)


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
            | ID DOT ID
            | ID DOT CASES
            | QUOTED_STRING
            | antiquotation
            | AT QUOTED_STRING
            | AT antiquotation
            | NEWLINE'''

    if len(p) == 4 and p[1] == '(' and p[3] == ')':
        body = p[2]
        name = None
    else:
        name = ''.join(p[1:])
        body = None

    p[0] = ('atom', {
        'name': name,
        'body': body,
    })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.2
#


def p_context(p):
    '''context : CONTEXT name BEGIN local_theory END
               | CONTEXT name opening BEGIN local_theory END
               | CONTEXT includes BEGIN local_theory END
               | CONTEXT includes context_elem_list BEGIN local_theory END
               | CONTEXT context_elem_list BEGIN local_theory END
               | CONTEXT BEGIN local_theory END
               | empty'''
    theory = p[len(p)-2]
    name = None
    includes = None
    context_elements = None
    if len(p) == 2:
        return None
    if len(p) == 6:
        if isinstance(p[2], str):
            name = p[2]
        elif p[2][0] == 'includes':
            includes = p[2]
        else:
            context_elements = p[2]
    elif len(p) == 7:
        if isinstance(p[2], str):
            name = p[2]
            if p[3][0] == 'opening':
                context_elements = p[3]
            else:
                includes = p[3]
        else:
            includes = p[2]
            context_elements = p[3]
    p[0] = ('context', {
        'name': name,
        'includes': includes,
        'context_elements': context_elements,
        'theory': theory,
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.3
#


def p_includes(p):
    '''includes : INCLUDES names_list'''
    p[0] = ('includes', {'names': p[2]})
    add_position(p)


def p_opening(p):
    '''opening : OPENING names_list'''
    p[0] = ('opening', {'names': p[2]})
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.4
#


def p_decl(p):
    '''decl : name WHERE
            | name WHERE comment_block
            | name mixfix WHERE
            | name COLONCOLON ID WHERE
            | name COLONCOLON QUOTED_STRING comment_block WHERE
            | name COLONCOLON QUOTED_STRING WHERE
            | name COLONCOLON QUOTED_STRING mixfix WHERE
            | name COLONCOLON ID mixfix WHERE'''
    name = p[1]
    type = None
    mixfix = None
    if len(p) == 4 and p[2][0] == 'mixfix':
        mixfix = p[2]
    if p[2] == ':' and p[3] == ':':
        type = p[4]
    if len(p) == 7 and p[5][0] == 'mixfix':
        mixfix = p[5]
    p[0] = ('decl', {
        'name': name,
        'type': type,
        'mixfix': mixfix,
        })
    add_position(p)


def p_definition(p):
    '''definition : DEFINITION decl thmdecl prop spec_prems for_fixes
                  | DEFINITION decl prop spec_prems for_fixes
                  | DEFINITION thmdecl prop spec_prems for_fixes
                  | DEFINITION prop spec_prems for_fixes
                  | DEFINITION LEFT_PAREN IN ID RIGHT_PAREN decl thmdecl prop spec_prems for_fixes
                  | DEFINITION LEFT_PAREN IN ID RIGHT_PAREN decl prop spec_prems for_fixes
                  | DEFINITION LEFT_PAREN IN ID RIGHT_PAREN thmdecl prop spec_prems for_fixes
                  | DEFINITION LEFT_PAREN IN ID RIGHT_PAREN prop spec_prems for_fixes'''
    if p[2] == '(' and p[3] == 'in' and p[5] == ')':
        immediate_target = p[4]
        offset = 4
    else:
        immediate_target = None
        offset = 0

    if p[2 + offset][0] == 'decl':
        decl = p[2 + offset]
        if len(p) == 7 + offset:
            thmdecl = p[3 + offset]
            prop = p[4 + offset]
        else:
            thmdecl = None
            prop = p[3 + offset]
    else:
        decl = None
        if len(p) == 6 + offset:
            thmdecl = p[2 + offset]
            prop = p[3 + offset]
        else:
            thmdecl = None
            prop = p[2 + offset]

    spec_prems = p[len(p)-2]
    for_fixes = p[len(p)-1]

    p[0] = ('definition', {
        'decl': decl,
        'thmdecl': thmdecl,
        'prop': prop,
        'spec_prems': spec_prems,
        'for_fixes': for_fixes,
        'immediate_target': immediate_target,
        })
    add_position(p)


def p_abbreviation(p):
    '''abbreviation : ABBREVIATION prop for_fixes
                    | ABBREVIATION mode prop for_fixes
                    | ABBREVIATION decl prop for_fixes
                    | ABBREVIATION mode decl prop for_fixes
                    | ABBREVIATION LEFT_PAREN IN ID RIGHT_PAREN prop for_fixes
                    | ABBREVIATION LEFT_PAREN IN ID RIGHT_PAREN mode prop for_fixes
                    | ABBREVIATION LEFT_PAREN IN ID RIGHT_PAREN decl prop for_fixes
                    | ABBREVIATION LEFT_PAREN IN ID RIGHT_PAREN mode decl prop for_fixes'''
    if p[2] == '(' and p[3] == 'in' and p[5] == ')':
        immediate_target = p[4]
        offset = 4
    else:
        immediate_target = None
        offset = 0

    prop = p[len(p)-2]
    for_fixes = p[len(p)-1]
    mode = None
    decl = None
    if p[2 + offset][0] == 'mode':
        mode = p[2 + offset]
    elif p[2 + offset][0] != 'mode':
        decl = p[2 + offset]
        if len(p) == 6 + offset:
            decl = p[3 + offset]

    p[0] = ('abbreviation', {
        'mode': mode,
        'decl': decl,
        'prop': prop,
        'for_fixes': for_fixes,
        'immediate_target': immediate_target,
        })
    add_position(p)

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
        })
    add_position(p)


def p_axiomatization(p):
    '''axiomatization : axiomatization_header spec_prems for_fixes'''
    p[0] = ('axiomatization', {
        'header': p[1],
        'spec_prems': p[2],
        'for_fixes': p[3],
        })
    add_position(p)


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
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.6
#


def p_declaration(p):
    '''declaration : DECLARATION LEFT_PAREN PERVASIVE RIGHT_PAREN CARTOUCHE
                   | DECLARATION CARTOUCHE
                   | SYNTAX_DECLARATION LEFT_PAREN PERVASIVE RIGHT_PAREN CARTOUCHE
                   | SYNTAX_DECLARATION CARTOUCHE
                   '''
    text = p[len(p)-1]
    pervasive = len(p) == 6
    p[0] = (p[1], {
        'pervasive': pervasive,
        'text': text,
        })
    add_position(p)


def p_declare(p):
    '''declare : DECLARE thms_list_and_sep'''
    p[0] = ('declare', {
        'thms': p[2],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.1
#


# move empty case of for_fixes here to avoid parsing error
def p_locale_expr(p):
    '''locale_expr : instance_list for_fixes'''
    p[0] = ('locale_expr', {
        'instances': p[1],
        'for_fixes': p[2],
        })
    add_position(p)


def p_instance_list(p):
    '''instance_list : instance PLUS instance_list
                     | instance'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_instance(p):
    '''instance : name pos_insts
                | name name_insts
                | name
                | qualifier COLON ID pos_insts
                | qualifier COLON ID name_insts'''
    if len(p) == 2:
        p[0] = ('instance', {
            'name': p[1],
            'insts': ('pos_insts', []),
        })
    elif len(p) == 3:
        p[0] = ('instance', {
            'name': p[1],
            'insts': p[2],
        })
    elif len(p) == 4:
        p[0] = ('instance', {
            'qualifier': p[1],
            'name': p[3],
            'insts': p[4],
        })
    add_position(p)


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
    '''name_insts_list : name EQUALS name
                       | name EQUALS name AND name_insts_list
                       | name EQUALS NAT
                       | name EQUALS NAT AND name_insts_list
                       | name EQUALS QUOTED_STRING
                       | name EQUALS QUOTED_STRING AND name_insts_list
                       | name EQUALS SYM_IDENT
                       | name EQUALS SYM_IDENT AND name_insts_list
                       | SYM_IDENT EQUALS ID
                       | SYM_IDENT EQUALS ID AND name_insts_list
                       | SYM_IDENT EQUALS QUOTED_STRING
                       '''
    if len(p) == 4:
        p[0] = [('equals', p[1], p[3])]
    elif len(p) == 5:
        p[0] = [('equals', p[1], p[3])] + p[4]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.2
#


def p_locale_block(p):
    '''locale_block : LOCALE name comment_block BEGIN local_theory END
                    | LOCALE name BEGIN local_theory END
                    | LOCALE name EQUALS locale BEGIN local_theory END
                    | LOCALE name EQUALS locale
                    | LOCALE name'''
    name = p[2]
    locale = None
    comment = None
    local_theory = None

    if len(p) == 6:
        local_theory = p[4]
    elif len(p) == 7:
        comment = p[3]
        local_theory = p[5]
    elif len(p) == 5:
        locale = p[4]
    elif len(p) == 8:
        locale = p[4]
        local_theory = p[6]

    p[0] = ('locale', {
        'name': name,
        'locale': locale,
        'local_theory': local_theory,
        'comment': comment,
    })

    add_position(p)


# flattened locale_expr to avoid parsing conflict between instance_list
# and PLUS below due to PLY using LALR(1)
def p_locale(p):
    '''locale : opening PLUS context_elem_list
              | opening
              | instance for_fixes PLUS context_elem_list
              | instance for_fixes opening
              | instance for_fixes opening PLUS context_elem_list
              | instance for_fixes
              | context_elem_list
              '''
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
                    | ASSUMES named_prop_list_and_sep
                    | DEFINES defines_list
                    | NOTES notes_list'''
    p[0] = ('context_elem', {
               'type': p[1],
               'content': p[2],
                })
    add_position(p)


def p_name_type_list(p):
    '''name_type_list : ID COLONCOLON ID
                      | ID COLONCOLON ID DOT ID
                      | ID COLONCOLON ID AND name_type_list'''

    name = p[1]
    if len(p) == 4:
        type = p[4]
    elif len(p) == 7 and p[5] == '.':
        type = "".join(p[4:7])
    else:
        type = p[4]

    head = ('name_type', {
        'name': name,
        'type': type,
    })
    add_position(p)

    if len(p) == 7 and p[5] == 'and':
        rest = p[6]
    else:
        rest = []

    p[0] = [head] + rest


def p_props_list_and_sep(p):
    '''props_list_and_sep : props
                          | props AND props_list_and_sep'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


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
                    })
    elif len(p) == 3:
        p[0] = ('definition', {
                    'thmdecl': p[1] if p[1][0] == 'thmdecl' else None,
                    'prop': p[2] if p[1][0] == 'thmdecl' else p[1],
                    'prop_pat': None if p[1][0] == 'thmdecl' else p[2],
                    })
    elif len(p) == 4:
        p[0] = ('definition', {
                    'thmdecl': p[1],
                    'prop': p[2],
                    'prop_pat': p[3],
                    })
    add_position(p)


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
                    })
    else:
        p[0] = ('note', {
                    'thmdef': p[1],
                    'thms': p[2],
                    })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.3
#


def p_interpretation_block(p):
    '''interpretation_block : INTERPRETATION locale_expr proof_prove'''
    p[0] = ('interpretation', {
        'locale_expr': p[2],
        'proof_prove': p[3],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.9
#


def p_consts(p):
    '''consts : CONSTS const_decls'''
    p[0] = ('consts', {
        'const_decls': p[2],
        })
    add_position(p)


def p_const_decls(p):
    '''const_decls : const_decl
                   | const_decl const_decls'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_const_decl(p):
    '''const_decl : name COLONCOLON type
                  | name COLONCOLON type mixfix'''
    if len(p) == 6:
        mixfix = p[5]
    else:
        mixfix = None
    name = p[1]
    type = p[4]
    p[0] = ('const_decl', {
        'name': name,
        'type': type,
        'mixfix': mixfix,
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.8
#


def p_instantiation(p):
    '''instantiation : INSTANTIATION name_list_and_sep COLONCOLON arity BEGIN local_theory END'''
    p[0] = ('instantiation', {
        'names': p[2],
        'arity': p[5],
        'local_theory': p[6],
        })


def p_name_list_and_sep(p):
    '''name_list_and_sep : name AND name_list_and_sep
                         | name'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_class_instance(p):
    '''class_instance : INSTANCE
                | INSTANCE name_list_and_sep COLONCOLON arity
                | INSTANCE name LT name
                | INSTANCE name SUBSETEQ name
                '''
    if len(p) == 2:
        p[0] = ('instance', {})
    elif len(p) == 5:
        if p[4] == '::':
            p[0] = ('instance', {
                'names': p[2],
                'arity': p[4],
                })
        else:
            p[0] = ('instance', {
                'name1': p[2],
                'relation': p[3],
                'name2': p[4],
                })
    add_position(p)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.10
#


def p_ml_code(p):
    '''ml : ML CARTOUCHE
          | SETUP CARTOUCHE'''
    p[0] = (p[1], {
        'command': p[2],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.12.2
#

def p_typedecl(p):
    '''typedecl : TYPEDECL typespec
                | TYPEDECL typespec mixfix'''
    p[0] = ('typedecl', {
                'typespec': p[2],
                'mixfix': p[3] if len(p) > 3 else None,
                })
    add_position(p)


def p_type_synonym(p):
    '''type_synonym : TYPE_SYNONYM typespec EQUALS ID
                    | TYPE_SYNONYM typespec EQUALS QUOTED_STRING
                    | TYPE_SYNONYM typespec EQUALS ID mixfix'''
    p[0] = ('type_synonym', {
                'typespec': p[2],
                'type': p[4],
                'mixfix': p[5] if len(p) > 5 else None,
                })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.13
#


# TODO complete
def p_lemmas(p):
    '''lemmas : LEMMAS thms for_fixes
              | LEMMAS thmdef thms for_fixes'''
    p[0] = ('lemmas', {
        'thmdef': p[2] if len(p) == 5 else None,
        'thms': p[len(p)-2],
        'for_fixes': p[len(p)-1],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.15
#


def p_hide_declarations(p):
    '''hide_declarations : HIDE_CLASS LEFT_PAREN OPEN RIGHT_PAREN name_list
                         | HIDE_TYPE LEFT_PAREN OPEN RIGHT_PAREN name_list
                         | HIDE_CONST LEFT_PAREN OPEN RIGHT_PAREN name_list
                         | HIDE_FACT LEFT_PAREN OPEN RIGHT_PAREN name_list
                         | HIDE_CLASS name_list
                         | HIDE_TYPE name_list
                         | HIDE_CONST name_list
                         | HIDE_FACT name_list'''
    open = len(p) == 6 and p[3] == 'open'
    p[0] = ('hide_declarations', {
        'open': open,
        'names': p[len(p)-1],
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.1.3
#


def p_oops(p):
    '''oops : OOPS'''
    p[0] = ('oops', {})
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.1
#


def p_fix(p):
    '''fix : FIX vars'''
    p[0] = ('fix', {'vars': p[2]})
    add_position(p)


def p_assume(p):
    '''assume : ASSUME concl prems for_fixes
              | PRESUME concl prems for_fixes'''
    p[0] = (p[1], {
        'concl': p[2] if len(p) == 5 else p[4],
        'prems': p[3] if len(p) == 5 else p[5],
        'for_fixes': p[4] if len(p) == 5 else p[6],
        })
    add_position(p)


def p_concl(p):
    '''concl : named_prop_list_and_sep'''
    p[0] = ('concl', {'props': p[1]})
    add_position(p)


# TODO should be props'_list in first line instead, but don't find definition
# also, should be props_list in second line, but don't find definition
def p_prems(p):
    '''prems : DEFINE vars WHERE prop_list for_fixes
             | IF prop_list DEFINE vars WHERE prop_list for_fixes
             | empty'''
    if len(p) == 2:
        p[0] = None
        return
    if len(p) == 6:
        p[0] = ('prems', {
            'vars': p[2],
            'props': p[4],
            'for_fixes': p[5],
            })
    else:
        p[0] = ('prems', {
            'conditions': p[2],
            'vars': p[4],
            'props': p[6],
            'for_fixes': p[7],
            })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.2
#


def p_let(p):
    '''let : LET let_statements'''
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
        })
    add_position(p)


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
                   | let proof_state
                   | assume proof_state
                   | case proof_state
                   | consider proof_prove
                   | from proof_chain
                   | have proof_prove
                   | show proof_prove
                   | proof proof_state
                   | subgoal proof_prove
                   | qed proof_state
                   | qed local_theory
                   | qed theory
                   | qed
                   | oops theory
                   | oops
                   | DONE proof_state
                   | DONE theory
                   | DONE local_theory
                   | DONE
                   | ALSO proof_state
                   | THEN proof_chain
                   | terminal_proof_steps
                   | hence proof_prove
                   | thus proof_prove
                   | obtain proof_prove
                   | note proof_state
                   | with proof_chain
                   | prems proof_state
                   | fix proof_state
                   | moreover proof_state
                   | ultimately proof_chain
                   | doc_block proof_state
                   '''
    if len(p) == 3:
        p[0] = ('proof_state', {
            'kind': p[1] if p[1] in ['note', 'next'] else None,
            'step': None if p[1] in ['note', 'next'] else p[1],
            'proof': p[2],
        })
    elif len(p) == 4:
        if p[1] == '{' and p[3] == '}':
            p[0] = ('proof_state', {
                'proof_state': p[2],
            })
    else:
        p[0] = p[1]
    add_position(p)


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
    add_position(p)


def p_proof_chain(p):
    '''proof_chain : have proof_prove
                   | consider proof_prove
                   | obtain proof_prove
                   | show proof_prove
                   | subgoal proof_prove
                   '''
    p[0] = (p[1], p[2])


def p_note(p):
    '''note : NOTE thms_list_and_sep'''
    p[0] = ('note', {
        'thms': p[2],
        })
    add_position(p)


def p_with(p):
    '''with : WITH thms_list_and_sep'''
    p[0] = ('with', {
        'thms': p[2],
        })
    add_position(p)


# TODO the first line is adhoc based on AFP, and doesn't match the grammar
def p_local_theory(p):
    '''local_theory : goal proof_prove
                    | statement local_theory
                    | statement
                    | declare local_theory
                    | doc_block local_theory
                    | class_instance local_theory
        '''
    if len(p) == 5 and p[1] == 'lemma':
        lemma = ('lemma', {
                'name': p[2],
                'statement': p[3],
            })
        p[0] = ('local_theory', [{
            'kind': p[1],
            'lemma': lemma,
            'proof': p[4],
            }])
    elif len(p) == 4:
        p[0] = ('local_theory', [{
            'kind': p[1],
            'statement': p[2],
            'proof': p[3],
            }])
    elif len(p) == 3 and p[2] and p[2][0] == 'local_theory':
        p[0] = ('local_theory', [p[1]] + p[2][1])
    elif len(p) == 2:
        p[0] = ('local_theory', [p[1]])


# NOTE ALSO proof_state here contradicts grammar in Isabelle/Isar
def p_proof_prove(p):
    '''proof_prove : SHOW stmt cond_stmt
                   | SHOW stmt cond_stmt for_fixes
                   | HENCE stmt cond_stmt
                   | HENCE stmt cond_stmt for_fixes
                   | apply proof_prove
                   | apply
                   | supply_block proof_prove
                   | supply_block
                   | subgoal proof_prove
                   | defer_block proof_prove
                   | defer_block
                   | prefer_block proof_prove
                   | prefer_block
                   | ALSO proof_state
                   | DONE proof_state
                   | DONE theory
                   | DONE local_theory
                   | DONE
                   | qed proof_state
                   | qed local_theory
                   | qed theory
                   | qed
                   | by proof_state
                   | by theory
                   | by local_theory
                   | by
                   | using proof_prove
                   | using
                   | with proof_chain
                   | proof proof_state
                   | proof
                   | nitpick proof_prove
                   | oops theory
                   | oops
                   | terminal_proof_steps proof_state
                   | terminal_proof_steps local_theory
                   | terminal_proof_steps theory
                   | terminal_proof_steps
                   | doc_block proof_prove
                   '''
    p[0] = p[1:]


# QUOTED_STRING only found in AFP, not in Isabelle/Isar grammar
def p_conclusion(p):
    '''conclusion : QUOTED_STRING
                  | CARTOUCHE
                  | SHOWS prop_list_with_pat
                  | OBTAINS obtain_clauses'''
    if p[1] == 'shows':
        shows = p[2]
        obtains = None
    elif len(p) == 2:
        shows = p[1]
        obtains = None
    else:
        obtains = p[2]
        shows = None

    p[0] = ('conclusion', {
        'shows': shows,
        'obtains': obtains,
        })
    add_position(p)


def p_obtain_clauses(p):
    '''obtain_clauses : obtain_case
                      | par_name obtain_case
                      | par_name obtain_case PIPE obtain_clauses
                      | obtain_case PIPE obtain_clauses'''
    if len(p) == 2:
        p[0] = [('obtain_clause', {
            'par_name': None,
            'obtain_case': p[1],
            })]
    elif len(p) == 3:
        p[0] = [('obtain_clause', {
            'par_name': p[1],
            'obtain_case': p[2],
            })]
    elif len(p) == 4:
        p[0] = [('obtain_clause', {
            'par_name': None,
            'obtain_case': p[1],
            })] + p[3]
    else:
        p[0] = [('obtain_clause', {
            'par_name': p[1],
            'obtain_case': p[2],
            })] + p[4]
    add_position(p)


def p_obtain_case(p):
    '''obtain_case : obtain_case_statements
                   | vars WHERE obtain_case_statements'''
    p[0] = ('obtain_case', {
        'vars': p[1] if len(p) == 4 else None,
        'obtain_case_statements': p[2] if len(p) == 4 else p[1],
    })
    add_position(p)


def p_obtain_case_statements(p):
    '''obtain_case_statements : obtain_case_statement
                              | obtain_case_statement AND obtain_case_statements'''
    p[0] = [p[1]] + p[3] if len(p) == 4 else [p[1]]


def p_obtain_case_statement(p):
    '''obtain_case_statement : prop_list
                             | thmdecl prop_list'''
    p[0] = ('obtain_case_statement', {
        'thmdecl': p[1] if len(p) == 3 else None,
        'prop_list': p[len(p)-1],
    })
    add_position(p)


def p_from(p):
    '''from : FROM thms_list_and_sep'''
    p[0] = ('from', {
        'thms': p[2],
        })
    add_position(p)


def p_using(p):
    '''using : USING thms_list_and_sep
             | UNFOLDING thms_list_and_sep'''
    p[0] = (p[1], {
        'thms': p[2],
        })
    add_position(p)


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
    p[0] = ('assms', {})
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.4
#


def p_goal(p):
    '''goal : LEMMA LEFT_PAREN IN ID RIGHT_PAREN long_statement
            | LEMMA LEFT_PAREN IN ID RIGHT_PAREN short_statement
            | THEOREM LEFT_PAREN IN ID RIGHT_PAREN long_statement
            | THEOREM LEFT_PAREN IN ID RIGHT_PAREN short_statement
            | COROLLARY LEFT_PAREN IN ID RIGHT_PAREN long_statement
            | COROLLARY LEFT_PAREN IN ID RIGHT_PAREN short_statement
            | PROPOSITION LEFT_PAREN IN ID RIGHT_PAREN long_statement
            | PROPOSITION LEFT_PAREN IN ID RIGHT_PAREN short_statement
            | SCHEMATIC_GOAL LEFT_PAREN IN ID RIGHT_PAREN long_statement
            | SCHEMATIC_GOAL LEFT_PAREN IN ID RIGHT_PAREN short_statement
            | LEMMA long_statement
            | LEMMA short_statement
            | THEOREM long_statement
            | THEOREM short_statement
            | COROLLARY long_statement
            | COROLLARY short_statement
            | PROPOSITION long_statement
            | PROPOSITION short_statement
            | SCHEMATIC_GOAL long_statement
            | SCHEMATIC_GOAL short_statement

    '''
    if len(p) > 5 and p[2] == '(' and p[5] == ')' and p[4] == 'in':
        target = p[5]
    else:
        target = None
    p[0] = (p[1], {
        'statement': p[len(p)-1],
        'target': target,
        })
    add_position(p)


def p_have(p):
    '''have : HAVE short_stmt cond_stmt for_fixes'''
    p[0] = ('have', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4],
        })
    add_position(p)


def p_show(p):
    '''show : SHOW stmt cond_stmt for_fixes'''
    p[0] = ('show', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4],
        })
    add_position(p)


def p_hence(p):
    '''hence : HENCE stmt cond_stmt
             | HENCE stmt cond_stmt for_fixes'''
    p[0] = ('hence', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4] if len(p) == 5 else None,
        })
    add_position(p)


def p_thus(p):
    '''thus : THUS stmt cond_stmt
            | THUS stmt cond_stmt for_fixes'''
    p[0] = ('thus', {
        'stmt': p[2],
        'cond_stmt': p[3],
        'for_fixes': p[4] if len(p) == 5 else None,
        })
    add_position(p)


def p_short_stmt(p):
    '''short_stmt : props_list_and_sep'''
    p[0] = ('stmt', p[1])
    add_position(p)


def p_stmt(p):
    '''stmt : named_prop_list_and_sep'''
    p[0] = ('stmt', p[1])
    add_position(p)


def p_cond_stmt(p):
    '''cond_stmt : empty
                 | IF stmt
                 | WHEN stmt'''
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = ('if', p[2])
        add_position(p)


# short_stmt (over stmt) disambiguates parsing with lemma name in long_statement
def p_short_statement(p):
    '''short_statement : short_stmt for_fixes
                       | short_stmt IF short_stmt for_fixes'''
    p[0] = ('short_statement', {

        'stmt': p[1],
        'if_stmt': p[3] if len(p) == 5 else None,
        'for_fixes': p[4] if len(p) == 5 else p[2],
    })
    add_position(p)


def p_long_statement(p):
    '''long_statement : thmdecl statement_context conclusion
                      | statement_context conclusion'''
    p[0] = ('long_statement', {
        'thmdecl': p[1] if len(p) == 4 else None,
        'context': p[2] if len(p) == 4 else None,
        'conclusion': p[3] if len(p) == 2 else None,
        })
    add_position(p)


def p_statement_context(p):
    '''statement_context : includes context_elem_list
                         | includes
                         | context_elem_list
                         | empty'''
    includes = None
    context_elements = None
    if len(p) == 2:
        if p[1] is None:
            p[0] = None
            return
        if isinstance(p[1], list):
            context_elements = p[1]
        else:
            includes = p[1]
    elif len(p) == 3:
        includes = p[1]
        context_elements = p[2]

    p[0] = ('statement_context', {
        'includes': includes,
        'context_elements': context_elements,
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.3
#


# TODO complete
def p_moreover(p):
    '''moreover : MOREOVER'''
    p[0] = ('moreover', {})
    add_position(p)


def p_ultimately(p):
    '''ultimately : ULTIMATELY'''
    p[0] = ('ultimately', {})
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.1
#


# TODO missing induct, induction, and coinduct
def p_method(p):
    '''method : LEFT_PAREN methods RIGHT_PAREN method_modifier
              | LEFT_PAREN methods RIGHT_PAREN
              | name method_modifier
              | name
              | cases
              '''
    name = None
    methods = None
    method_modifier = get_value_by_rule(p, 'method_modifier')

    if p[1][0] == 'cases':
        methods = p[1]
    if p[1] == '(' and p[3] == ')':
        methods = p[2]
    else:
        name = p[1]
    p[0] = ('method', {
        'name': name,
        'methods': methods,
        'modifier': method_modifier,
        })
    add_position(p)


def p_method_modifier(p):
    '''method_modifier : QUESTION_MARK
                       | PLUS
                       | LEFT_BRACKET NAT RIGHT_BRACKET'''
    if len(p) == 2:
        p[0] = ('method_modifier', {
            'modifier': p[1],
        })
    else:
        p[0] = ('method_modifier', {
            'modifier': 'times',
            'nat': p[2],
        })
    add_position(p)


# TODO keywords overlap: INDUCT
def p_methods(p):
    '''methods : method COMMA methods
               | method SEMICOLON methods
               | method PIPE methods
               | method
               | name method_args COMMA methods
               | INDUCT method_args COMMA methods
               | INDUCTION method_args COMMA methods
               | RULE method_args COMMA methods
               | name method_args SEMICOLON methods
               | INDUCT method_args SEMICOLON methods
               | INDUCTION method_args SEMICOLON methods
               | RULE method_args SEMICOLON methods
               | name method_args PIPE methods
               | INDUCT method_args PIPE methods
               | INDUCTION method_args PIPE methods
               | RULE method_args PIPE methods
               | name method_args
               | INDUCT method_args
               | INDUCTION method_args
               | RULE method_args
               '''
    method = None
    sep = None
    methods = None
    if p[1][0] == 'method':
        method = p[1]
        if len(p) > 2:
            sep = p[2]
            methods = p[3]
    else:
        method = ('method', {
            'name': p[1],
            'args': p[2],
            })
        if len(p) == 5:
            sep = p[3]
            methods = p[4]
    p[0] = ('methods', {
        'method': method,
        'sep': sep,
        'methods': methods,
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.2
#


def p_proof(p):
    '''proof : PROOF SYM_IDENT method
             | PROOF method
             | PROOF DASH
             | PROOF'''
    p[0] = ('proof', {
        'method': p[len(p)-1] if len(p) > 2 else None,
        'ident': p[2] if len(p) == 4 else None,
        })
    add_position(p)


def p_qed(p):
    '''qed : QED method
           | QED'''
    p[0] = ('qed', {
        'method': p[2] if len(p) == 3 else None,
        })
    add_position(p)


def p_by(p):
    '''by : BY method
          | BY method method'''
    if len(p) > 3 and p[3][0] == 'method':
        methods = [p[2], p[3]]
    else:
        methods = [p[2]]

    p[0] = ('by', {
        'methods':  methods,
        })
    add_position(p)


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
            | CASE TRUE
            | CASE FALSE
            | CASE NAT
            | CASE LEFT_PAREN name_underscore_list RIGHT_PAREN'''
    p[0] = ('case', {
        'names': [p[2]] if len(p) == 3 else p[3],
        })
    add_position(p)


def p_name_underscore_list(p):
    '''name_underscore_list : name
                            | NAT
                            | UNDERSCORE
                            | name name_underscore_list
                            | NAT name_underscore_list
                            | UNDERSCORE name_underscore_list'''
    p[0] = [p[1]] + p[2] if len(p) == 3 else [p[1]]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.2
#


def p_cases(p):
    '''cases : CASES no_simp_block insts_list_and_sep rule
             | CASES no_simp_block rule
             | CASES no_simp_block insts_list_and_sep
             | CASES no_simp_block
             | CASES insts_list_and_sep rule
             | CASES insts_list_and_sep
             | CASES QUOTED_STRING rule
             | CASES QUOTED_STRING
             | CASES rule
             | CASES
             '''
    rule = get_value_by_rule(p, 'rule')
    no_simp = p[2] if len(p) > 2 and isinstance(p[2], bool) else False
    insts = get_value_by_type(p, list, [])
    inst = get_value_by_type(p, str, None)
    if inst and insts == []:
        insts = [inst]
    p[0] = ('cases', {
        'no_simp': no_simp,
        'insts': insts,
        'rule': rule,
        })
    add_position(p)


def p_insts_list_and_sep(p):
    '''insts_list_and_sep : insts AND insts_list_and_sep
                          | insts
                          | empty'''
    if len(p) == 2:
        p[0] = [p[1]] if p[1] else []
    else:
        p[0] = [p[1]] + p[3]


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
    add_position(p)


def p_arbitary_block(p):
    '''arbitary_block : empty
                      | arbitrary'''
    p[0] = p[1]


def p_arbitrary(p):
    '''arbitrary : ARBITRARY COLON term_list_and'''
    p[0] = ('arbitrary', {
        'terms': p[3],
        })
    add_position(p)


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
            })
    add_position(p)


def p_rule_block(p):
    '''rule_block : empty
                  | rule'''
    p[0] = p[1]


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.6
#


def p_consider(p):
    '''consider : CONSIDER obtain_clauses'''
    p[0] = ('consider', {
        'clauses': p[2],
        })
    add_position(p)


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
            })
    elif len(p) == 5:
        p[0] = ('obtain', {
            'par_name': p[2] if p[2][0] == 'par_name' else None,
            'concl': p[3] if p[2][0] == 'par_name' else p[2],
            'prems': p[4] if p[2][0] == 'par_name' else p[3],
            'for_fixes': None if p[2][0] == 'par_name' else p[4],
            })
    elif len(p) == 6:
        p[0] = ('obtain', {
            'par_name': p[2] if p[2][0] == 'par_name' else None,
            'vars': None if p[2][0] == 'par_name' else p[2],
            'concl': p[4] if p[3] == 'where' else p[3],
            'prems': p[5] if p[3] == 'where' else p[4],
            'for_fixes': None if p[3] == 'where' else p[5],
            })
    elif len(p) == 7:
        p[0] = ('obtain', {
            'par_name': p[4] if p[4][0] == 'par_name' else None,
            'vars': p[2],
            'concl': p[5] if p[4][0] == 'par_name' else p[4],
            'prems': p[6] if p[4][0] == 'par_name' else p[5],
            'for_fixes': None if p[4][0] == 'par_name' else p[6],
            })
    else:
        p[0] = ('obtain', {
            'vars': p[2],
            'par_name': p[4],
            'concl': p[5],
            'prems': p[6],
            'for_fixes': p[7],
            })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 7.1
#


def p_apply(p):
    '''apply : APPLY method
             | APPLY_END method'''
    p[0] = ('apply', {
        'end': p[1] == 'apply_end',
        'method': p[2],
        })
    add_position(p)


def p_supply_block(p):
    '''supply_block : SUPPLY proof_state_statements'''
    p[0] = ('supply', {
        'statements': p[2],
        })
    add_position(p)


def p_defer_block(p):
    '''defer_block : DEFER
                   | DEFER NAT'''
    p[0] = ('defer', {
        'number': p[2] if len(p) > 2 else None,
        })
    add_position(p)


def p_prefer_block(p):
    '''prefer_block : PREFER NAT'''
    p[0] = ('prefer', {
        'number': p[2],
        })
    add_position(p)


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
              | LEFT_PAREN BINDER template NAT RIGHT_PAREN
              | LEFT_PAREN BINDER template prio NAT RIGHT_PAREN
              | STRUCTURE'''
    if len(p) == 1:
        p[0] = ('mixfix', {
                    'type': p[1],
                    })
    elif p[2] in ['infix', 'infixl', 'infixr']:
        p[0] = ('mixfix', {
                    'type': p[2],
                    'template': p[3],
                    'nat': p[4],
                    })
    elif p[1] == 'binder':
        p[0] = ('mixfix', {
                    'type': p[1],
                    'template': p[2],
                    'prio': p[3] if len(p) > 4 else None,
                    'nat': p[4] if len(p) > 4 else p[3],
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
            })
    add_position(p)


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
                      | NOTATION mode notation_list
                      | NO_NOTATION notation_list
                      | NO_NOTATION mode notation_list
                      '''
    p[0] = (p[1], {
        'mode': p[2] if len(p) == 4 else None,
        'notations': p[len(p)-1],
    })
    add_position(p)


def p_notation_list(p):
    '''notation_list : notation
                     | notation AND notation_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_notation(p):
    '''notation : name mixfix'''
    p[0] = ('notation', {
        'name': p[1],
        'mixfix': p[2],
    })
    add_position(p)


# TODO
def p_mode(p):
    '''mode : ID
            | LEFT_PAREN INPUT RIGHT_PAREN'''
    p[0] = ('mode', p[1])
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.5.2
#


def p_syntax(p):
    '''syntax : SYNTAX mode constdecl_list
              | SYNTAX constdecl_list
              | NO_SYNTAX mode constdecl_list
              | NO_SYNTAX constdecl_list'''
    p[0] = (p[1], {
        'mode': p[2] if len(p) == 4 else None,
        'const_decls': p[len(p)-1],
    })
    add_position(p)


def p_translations(p):
    '''translations : TRANSLATIONS transpat EQUALS EQUALS transpat
                    | TRANSLATIONS transpat EQUALS GT transpat
                    | TRANSLATIONS transpat LT EQUALS transpat
                    | TRANSLATIONS transpat RIGHTLEFTHARPOONS GT transpat
                    | NO_TRANSLATIONS transpat EQUALS EQUALS transpat
                    | NO_TRANSLATIONS transpat EQUALS GT transpat
                    | NO_TRANSLATIONS transpat LT EQUALS transpat
                    | NO_TRANSLATIONS transpat RIGHTLEFTHARPOONS GT transpat
                    '''
    p[0] = (p[1], {
        'operand1': p[2],
        'operand2': p[len(p)-1],
        'comparison': "".join(p[3:len(p)-1]),
        })
    add_position(p)


def p_transpat(p):
    '''transpat : QUOTED_STRING
                | LEFT_PAREN name RIGHT_PAREN QUOTED_STRING'''
    if len(p) == 2:
        name = None
        string = p[1]
    else:
        name = p[2]
        string = p[4]
    p[0] = ('transpat', {
        'name': name,
        'string': string,
    })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 9.2.1
#


def p_folded(p):
    '''folded : FOLDED thms
              | UNFOLDED thms'''
    p[0] = (p[1], {'thms': p[2]})
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.1
#


def p_inductive(p):
    '''inductive : INDUCTIVE vars for_fixes WHERE multi_specs MONOS thms
                 | INDUCTIVE vars for_fixes WHERE multi_specs
                 | INDUCTIVE vars for_fixes MONOS thms'''
    vars = p[1]
    for_fixes = p[2]
    if p[4] == 'WHERE':
        multi_specs = p[5]
        thms = p[7] if len(p) == 8 and p[6] == 'monos' else p[6]
    else:
        multi_specs = None
        thms = p[5]
    p[0] = ('inductive', {
        'vars': vars,
        'for_fixes': for_fixes,
        'multi_specs': multi_specs,
        'thms': thms,
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2
#


def p_primrec(p):
    '''primrec : PRIMREC specification'''
    p[0] = ('primrec', p[2])
    add_position(p)


def p_fun_block(p):
    '''fun_block : FUN specification
                 | FUNCTION specification proof_prove
                 | FUN opts specification
                 | FUNCTION opts specification proof_prove'''
    p[0] = ('fun', {
        'specification': p[2] if len(p) == 3 else p[3],
        'opts': p[2] if len(p) == 4 else None,
        })
    add_position(p)


def p_opts(p):
    '''opts : LEFT_PAREN opt_list RIGHT_PAREN'''
    p[0] = ('opts', p[2])
    add_position(p)


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


# TODO generated from examples
# Grammar rules
def p_datatype(p):
    """
    datatype : DATATYPE generic_type EQUALS constructors
    """
    p[0] = {
        "datatype": p[2],
        "constructors": p[4],
    }
    add_position(p)


def p_generic_type(p):
    """
    generic_type : type name
                 | type
    """
    if len(p) == 3:
        p[0] = {"type": p[1], "parameter": p[2]}
    else:
        p[0] = {"type": p[1]}
    add_position(p)


def p_constructors(p):
    """
    constructors : constructor
                 | constructor PIPE constructors
    """
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[3]


def p_constructor(p):
    """
    constructor : ID TYPE_IDENT comment_block
                | ID TYPE_IDENT
                | ID ID comment_block
                | ID ID
                | ID QUOTED_STRING comment_block
                | ID QUOTED_STRING
                | ID comment_block
                | ID
    """
    if len(p) == 3:
        p[0] = {"name": p[1], "type": p[2]}
    else:
        p[0] = {"name": p[1]}
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2.2
#


def p_partial_function(p):
    '''partial_function : PARTIAL_FUNCTION LEFT_PAREN name RIGHT_PAREN specification'''
    p[0] = ('partial_function', {
        'name': p[3],
        'specification': p[5],
        })
    add_position(p)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.6.2
#


def p_record(p):
    '''record : RECORD overloaded typespec_sorts EQUALS type PLUS constdecl_list
              | RECORD typespec_sorts EQUALS type PLUS constdecl_list
              | RECORD overloaded typespec_sorts EQUALS constdecl_list
              | RECORD typespec_sorts EQUALS constdecl_list'''
    if len(p) == 6 or len(p) == 8 and p[2] == True:
        overloaded = p[2]
    else:
        overloaded = False

    if overloaded:
        typespec_sorts = p[3]
    else:
        typespec_sorts = p[2]

    if len(p) == 8:
        type = p[len(p) - 3]
        consts = p[len(p) - 1]
    elif len(p) == 7:
        type = p[4]
        consts = p[6]
    elif len(p) == 6:
        type = p[5]
        consts = []
    else:
        type = p[4]
        consts = []

    p[0] = ('record', {
        'overloaded': overloaded,
        'typespec_sorts': typespec_sorts,
        'type': type,
        'consts': consts,
        })
    add_position(p)


def p_constdecl_list(p):
    '''constdecl_list : constdecl
                      | constdecl constdecl_list'''
    p[0] = [p[1]] if len(p) == 2 else [p[1]] + p[2]


def p_constdecl(p):
    '''constdecl : name COLONCOLON type
                 | name COLONCOLON type comment_block
                 | name COLONCOLON type mixfix'''
    mixfix = get_value_by_rule(p, 'mixfix')
    comment = get_value_by_rule(p, 'comment')
    p[0] = ('constdecl', {
        'name': p[1],
        'type': p[3],
        'mixfix': mixfix,
        'comment': comment,
        })
    add_position(p)


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.7
#


def p_overloaded(p):
    '''overloaded : LEFT_PAREN OVERLOADED RIGHT_PAREN'''
    p[0] = True


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 12.2
#


def p_nitpick(p):
    '''nitpick : NITPICK LEFT_BRACKET args RIGHT_BRACKET NAT
               | NITPICK LEFT_BRACKET args RIGHT_BRACKET
               | NITPICK NAT
               | NITPICK'''
    args = None
    nat = None
    if len(p) == 6:
        args = p[3]
        nat = p[5]
    elif len(p) == 5:
        args = p[3]
    elif len(p) == 3:
        nat = p[2]
    p[0] = ('nitpick', {
        'args': args,
        'nat': nat,
        })
    add_position(p)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 13
#


def p_export_code(p):
    '''export_code : OPEN const_expr_list export_target_list
                   | const_expr_list export_target_list'''
    is_open = p[1] == 'open'
    consts = p[len(p)-2]
    export_targts = p[len(p)-1]
    p[0] = ('export_code', {
        'open': is_open,
        'consts': consts,
        'export_targets': export_targts,
        })
    add_position(p)


def p_const_expr_list(p):
    '''const_expr_list : const_expr
                       | const_expr const_expr_list'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]


def p_export_target_list(p):
    '''export_target_list : export_target export_target_list
                          | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = [p[1]] + p[2]


def p_export_target(p):
    '''export_target : IN target MODULE_NAME ID FILE_PREFIX path LEFT_PAREN args RIGHT_PAREN
                     | IN target MODULE_NAME ID FILE_PREFIX path
                     | IN target MODULE_NAME ID LEFT_PAREN args RIGHT_PAREN
                     | IN target MODULE_NAME ID
                     | IN target FILE_PREFIX path LEFT_PAREN args RIGHT_PAREN
                     | IN target FILE_PREFIX path
                     | IN target LEFT_PAREN args RIGHT_PAREN
                     | IN target
                     '''
    target = p[2]
    if len(p) > 3 and p[3] == 'module_name':
        module_name = p[4]
        if len(p) > 5 and p[5] == 'file_prefix':
            file_prefix = p[6]
            path = p[7]
            if len(p) > 8:
                args = p[9]
            else:
                args = None
        elif len(p) > 5 and p[5] == 'path':
            path = p[6]
            file_prefix = None
            if len(p) > 7:
                args = p[8]
            else:
                args = None
        else:
            file_prefix = None
            path = None
            if len(p) > 5:
                args = p[6]
            else:
                args = None
    elif len(p) > 3 and p[3] == 'file_prefix':
        file_prefix = p[4]
        path = p[5]
        module_name = None
        if len(p) > 6:
            args = p[7]
        else:
            args = None
    else:
        module_name = None
        file_prefix = None
        path = None
        if len(p) > 3:
            args = p[4]
        else:
            args = None
    p[0] = ('export_target', {
        'target': target,
        'module_name': module_name,
        'file_prefix': file_prefix,
        'path': path,
        'args': args,
        })
    add_position(p)


def p_target(p):
    '''target : SML
              | OCAML
              | HASKELL
              | SCALA
              | EVAL'''
    p[0] = ('target', {
        'target': p[1],
        })
    add_position(p)


def p_const_expr(p):
    '''const_expr : const
                  | ID DOT UNDERSCORE
                  | UNDERSCORE'''
    p[0] = ('const_expr', {
        'const_expr': p[1:],
        })
    add_position(p)


def p_const(p):
    '''const : term'''
    p[0] = p[1]


def p_path(p):
    '''path : embedded'''
    p[0] = p[1]


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
        type = p.type
        column = get_column(source, p.lexpos) if source else -1
        lineno = p.lineno
    else:
        value = "NONE"
        type = "NONE"
        column = -1
        lineno = -1
    raise ParsingError(f"Syntax error at '{value}' with type '{type}'",
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


#
# Utilities
#


def add_position(p):
    if isinstance(p[0], tuple) and isinstance(p[0][1], dict):
        p[0][1]['line'] = p.lineno(1)
        p[0][1]['column'] = get_column(source, p.lexpos(1)) if source else -1


def get_value_by_rule(p, rule_name, default=None):
    for i in range(1, len(p)):
        if p[i] and p[i][0] == rule_name:
            return p[i]
    return default


def get_value_by_type(p, type, default=None):
    for i in range(1, len(p)):
        if isinstance(p[i], type):
            return p[i]
    return default
