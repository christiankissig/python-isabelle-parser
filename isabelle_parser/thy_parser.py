from lark import Lark

import logging


logger = logging.getLogger(__name__)


grammar = r"""
%import common.CNAME -> NAME
%import common.INT -> INT
%import common.WS
%ignore WS
%ignore OUTER_COMMENT

QUOTED_STRING: "\"" /[\s\S]*?/ "\""

// Tokens for cartouche
CARTOUCHE_OPEN: "\\<open>"
CARTOUCHE_TEXT: /[^\\]+/
CARTOUCHE_CLOSE: "\\<close>"

cartouche: CARTOUCHE_OPEN cartouche_content CARTOUCHE_CLOSE

cartouche_content: (CARTOUCHE_TEXT | cartouche)*

// General Isabelle tokens
OUTER_COMMENT: /\(\*[\s\S]*?\*\)/   // Multiline comments
BOTTOM: "\\<bottom>"
EQUIV: "\\<equiv>"
NEWLINE: "\\<newline>"
COMMENT_CARTOUCHE: "\\<comment>"
MARKER: "\\<\\^marker>"
VAR_CASE: "\\?case"
VAR_THESIS: "\\?thesis"

// Greek symbols
GREEK: "\\<alpha>"
     | "\\<beta>"
     | "\\<gamma>"
     | "\\<delta>"
     | "\\<epsilon>"
     | "\\<zeta>"
     | "\\<eta>"
     | "\\<theta>"
     | "\\<iota>"
     | "\\<kappa>"
     | "\\<mu>"
     | "\\<nu>"
     | "\\<xi>"
     | "\\<pi>"
     | "\\<rho>"
     | "\\<sigma>"
     | "\\<tau>"
     | "\\<upsilon>"
     | "\\<phi>"
     | "\\<chi>"
     | "\\<psi>"
     | "\\<omega>"
     | "\\<Gamma>"
     | "\\<Delta>"
     | "\\<Theta>"
     | "\\<Lambda>"
     | "\\<Xi>"
     | "\\<Pi>"
     | "\\<Sigma>"
     | "\\<Upsilon>"
     | "\\<Phi>"
     | "\\<Psi>"
     | "\\<Omega>"

// Reserved Words
reserved: "Eval" | "False" | "Haskell" | "ML" | "OCaml" | "SML" | "Scala" | "True" | "abbreviation" | "also" | "and" | "apply" | "apply_end" | "arbitrary" | "assms" | "assume" | "assumes" | "at" | "axiomatization" | "begin" | "binder" | "by" | "case" | "cases" | "chapter" | "coinduct" | "consider" | "constrains" | "consts" | "context" | "corollary" | "datatype" | "declaration" | "declare" | "defer" | "define" | "defines" | "definition" | "done" | "end" | "file_prefix" | "fix" | "fixes" | "folded" | "for" | "from" | "fun" | "function" | "global_interpretation" | "have" | "hence" | "hide_class" | "hide_const" | "hide_fact" | "hide_type" | "if" | "imports" | "in" | "includes" | "induct" | "induction" | "inductive" | "infix" | "infixl" | "infixr" | "input" | "instance" | "instantiation" | "interpret" | "interpretation" | "is" | "lemma" | "lemmas" | "let" | "locale" | "method" | "module_name" | "monos" | "moreover" | "next" | "nitpick" | "no_notation" | "no_simp" | "no_syntax" | "no_translations" | "notation" | "note" | "notes" | "obtain" | "obtains" | "oops" | "open" | "opening" | "overloaded" | "paragraph" | "partial_function" | "pervasive" | "pred" | "prefer" | "presume" | "primrec" | "proof" | "proposition" | "qed" | "record" | "rule" | "schematic_goal" | "section" | "set" | "setup" | "show" | "shows" | "sorry" | "structure" | "subgoal" | "sublocale" | "subsection" | "subsubsection" | "supply" | "syntax" | "syntax_declaration" | "taking" | "text" | "then" | "theorem" | "theory" | "thus" | "translations" | "txt" | "type" | "type_synonym" | "typedecl" | "ultimately" | "unfolded" | "unfolding" | "using" | "when" | "where" | "with"

// Identifiers and strings
SHORT_IDENT: /[a-zA-Z](_?\d*[a-zA-Z_\']*)*/
LONG_IDENT: /([a-zA-Z](_?\d*[a-zA-Z\']*)*)(\.([a-zA-Z\'](_?\d*[a-zA-Z\']*)*))+/
#SYM_IDENT: /[!#$%&*+\-/<>?@^_`|~]+[a-zA-Z][a-zA-Z0-9]*/
SYM_IDENT: /[-!#$%&*+\/<>?@^_`|~]+[a-zA-Z][a-zA-Z0-9]*/
ID: /[a-zA-Z_][a-zA-Z_0-9\']*(\\<\\^sub>[a-zA-Z0-9_]*)?/
ALTSTRING: /`[^`]*`/
VERBATIM: /{\*.*\*}/
LETTER: /[a-zA-Z]/
LATIN: /[a-zA-Z]/

// Numbers and variables
NAT: /\d+/
SYM_FLOAT: /\d+(\.\d+)+|\.\d+/
TERM_VAR: /\?[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*/
TYPE_VAR: /'[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*/

// Other predefined tokens
TYPE_IDENT: /'[a-zA-Z](_?\d*[a-zA-Z_\']*)*/

// Define start rule
start: theory_file

// Top-level rule
theory_file: theory_block
           | doc_block theory_file
           | marker theory_file

theory_block: "theory" name imports_opt "begin" theory "end"

imports_opt: "imports" import_list

import_list: QUOTED_STRING import_list
           | comment_block import_list
           | NAME import_list
           | NAME "." NAME import_list
           | NAME "." NAME
           | NAME
           | QUOTED_STRING
           | comment_block

theory: (goal proof_prove
      | statement
      | class_instance proof_prove
      | derive)*

statement: abbreviation
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
         | global_interpretation proof_prove
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
         | sublocale proof_prove
         | syntax
         | translations
         | type_synonym
         | typedecl

method_block: "method" name "=" instruction

instruction: single_instruction
           | single_instruction instruction_modifier
           | single_instruction instruction_modifier "," instruction
           | single_instruction ";" instruction
           | single_instruction "," instruction
           | "(" instruction ")"
           | "(" instruction ")" instruction_modifier

instruction_modifier: "+"
                    | "?"

single_instruction: "(" name method_args ")"
                  | "(" name method_args ")" instruction_modifier
                  | name method_args
                  | name

var_list_nosep: var var_list_nosep
              | var

assumptions_list: assumption "and" assumptions_list
                | assumption

assumption: QUOTED_STRING
          | NAT ":" QUOTED_STRING
          | ID ":" QUOTED_STRING

subgoal: "subgoal" name ":"
       | "subgoal"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.1
#

name: ID
    | "case"
    | "cases"
    | GREEK "'"*
    | ID "."
    | ID "." "cases"
    | ID "." name
    | ID "\\<^sub>" NAT "'"?
    | ID "\\<^sub>" name
    | "in"
    | "induct"
    | NAT
    | "pred"
    | QUOTED_STRING
    | "*"
    | "**"
    | SYM_IDENT
    | "where"

par_name: "(" name ")"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.3
#

embedded: ID
        | QUOTED_STRING
        | cartouche
        | NAT
        | GREEK
        | "True"
        | "False"
        | VAR_CASE
        | VAR_THESIS
        | TYPE_IDENT
        | SYM_IDENT

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.7
#

type: embedded

term: QUOTED_STRING
    | GREEK
    | ID
    | TERM_VAR
    | SYM_IDENT
    | "?f'"

named_prop_list_and_sep: named_prop "and" named_prop_list_and_sep
                       | named_prop

named_prop: prop
          | prop_list
          | ID ":" prop
          | NAT ":" prop
          | "*" ":" prop
          | "**" ":" prop
          | "***" ":" prop

prop: embedded

inst: "_"
    | term

insts: inst insts

typespec: typeargs? ID

typearg: TYPE_IDENT
       | ID ("::" ID)?

# moved empty case to p_typespec in order to avoid parsing error
typeargs: typearg ("," typearg)* | "(" typeargs ")"

typeargs_sorts: type_ident_with_sort
              | "(" type_ident_with_sort_list ")"

type_ident_with_sort : TYPE_IDENT ("::" sort)?

type_ident_with_sort_list : type_ident_with_sort ("," type_ident_with_sort)*

typespec_sorts : typeargs_sorts name

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.6
#

sort : ID

sort_list_comma_sep : sort ("," sort)*

arity : ("(" sort_list_comma_sep ")")? sort

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.8
#

vars: var ("and"? var)*

var: (name | names) ("::" type)? mixfix?

props: thmdecl? (prop prop_pat?)+

prop_list_with_pat: prop prop_pat? ("and"? prop prop_pat?)*

names: ID ("and" names)?

name_list: name+

names_list: ID | ID names

prop_pat: "(" prop_pat_terms ")"

prop_pat_terms: prop_pat_term+

prop_pat_term: "is" (ID | QUOTED_STRING)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.9
#

method_arg_atom: name
               | NAT
               | cartouche
               | "assms"
               | "*"
               | name ":"
               | "arbitrary" ":"
               | "rule" ":"
               | ID "!" ":"
               | name "." "cases"
               | name "." "induct"
               | name ("\\<^sub>" name)*
               | name "(" NAT ")"
               | name "(" NAT "," NAT ")" ":"
               | name "=" name
               | cases

method_arg: method_arg_atom
          | "(" method_args ")"
          | "[" method_args "]"

method_args: (","? method_arg)*

attributes: "[" (name args ("," name args)*)? "]"

attributes_list : attribute ("," attribute)*

# TODO [OF assms(1)] should be handled separately
attribute : name args
             | name "?"
             | name "!"
             | name "=" ID
             | ID "assms" "(" NAT ")"
             | folded
             | NAT

args: arg*

arg: ID
   | cartouche
   | "False"
   | "for"
   | GREEK
   | ID "\\<^sub>" ID
   | "\\<infinity>"
   | "[" args "]"
   | "(" args ")"
   | NAT
   | QUOTED_STRING
   | SYM_IDENT
   | "True"
   | ":"

thmdecl: thmbind ":"

thmdef: thmbind "="

# TODO add altstring
thm: (((name selection?) | cartouche) attributes?) | ("[" attributes "]")

thms: thm+

thmbind: name attributes?
       | attributes

selection: "(" selection_list ")"

selection_list: selection_item ("," selection_item)*

selection_item: NAT ("-" NAT?)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.10
#

for_fixes: "for" vars

multi_specs: structured_spec ("|" structured_spec)*

structured_spec: thmdecl? prop spec_prems? for_fixes?

spec_prems : "if" prop_list

prop_list: prop ("and"? prop)*

specification: vars comment_block? "where" comment_block? multi_specs

# TODO p75
antiquotation_body : ID

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.1
#

doc_block: ("chapter" | "section" | "subsection" | "subsubsection" | "paragraph" | "text" | "txt" | "text_raw" | COMMENT_CARTOUCHE) (cartouche | QUOTED_STRING)

comment_block: COMMENT_CARTOUCHE cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.2
#

antiquotation : "at" "{" antiquotation_body "}"
#                 | "/" "<" "^" ID ">" cartouche
#                 | cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.4
#

marker : "marker" cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.5
#

rules : rule
         | rule ";" rules

rule : "type" ":" name_list
        | "pred" ":" name_list
        | "set" ":" name_list
        | "rule" ":" thms

body : concatenation
        | concatenation "|" body

concatenation : atom_list
                 | atom_list "*" atom
                 | atom_list "+" atom_list

atom_list : atom
             | atom "?"
             | atom atom_list
             | atom "?" atom_list

atom : "(" ")"
        | "(" body ")"
        | ID
        | ID "." ID
        | ID "." "cases"
        | QUOTED_STRING
        | antiquotation
        | "at" QUOTED_STRING
        | "at" antiquotation
        | NEWLINE

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.2
#

context : "context" name "begin" local_theory "end"
           | "context" name opening "begin" local_theory "end"
           | "context" includes "begin" local_theory "end"
           | "context" includes context_elem_list "begin" local_theory "end"
           | "context" context_elem_list "begin" local_theory "end"
           | "context" "begin" local_theory "end"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.3
#

includes :  "includes"  names_list

opening : "opening" names_list

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.4
#

decl : name ("::" (ID | QUOTED_STRING))? mixfix? "where" comment_block?

definition: "definition" ("(" "in" ID ")")? decl? thmdecl? prop spec_prems? for_fixes?

abbreviation: "abbreviation" ("(" "in" ID ")")? mode? decl? prop for_fixes?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.5
#

axiomatization_block: "axiomatization" vars? ("where" axiomatization)?

axiomatization: axiomatization_header spec_prems for_fixes

axiomatization_header: thmdecl (ID | QUOTED_STRING) ("and" axiomatization_header)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.6
#

declaration : ("declaration" | "syntax_declaration") ("(" "pervasive" ")")? cartouche

declare : "declare" thms ("and" thms)*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.1
#

# move empty case of for_fixes here to avoid parsing error
locale_expr: instance_list for_fixes?

instance_list: instance ("+" instance)*

instance: name (pos_insts | name_insts)?
        | qualifier ":" ID (pos_insts | name_insts)

qualifier: ID
         | QUOTED_STRING
         | ID "?"
         | QUOTED_STRING "?"

pos_insts: ("_" | term)*

name_insts : "where" name_insts_list

name_insts_list : name "=" name
                   | name "=" name "and" name_insts_list
                   | name "=" NAT
                   | name "=" NAT "and" name_insts_list
                   | name "=" QUOTED_STRING
                   | name "=" QUOTED_STRING "and" name_insts_list
                   | name "=" SYM_IDENT
                   | name "=" SYM_IDENT "and" name_insts_list
                   | SYM_IDENT "=" ID
                   | SYM_IDENT "=" ID "and" name_insts_list
                   | SYM_IDENT "=" QUOTED_STRING

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.2
#

locale_block: "locale" name ("=" locale)? (comment_block)? ("begin" (local_theory)? "end")?

# flattened locale_expr to avoid parsing conflict between instance_list
# and "+" below due to PLY using LALR(1)
locale: opening ("+" context_elem_list)?
      | instance? for_fixes? opening? ("+" context_elem_list)?
      | context_elem_list

context_elem_list: context_elem+

context_elem: "fixes" vars
            | "constrains" name_type_list
            | "assumes" named_prop_list_and_sep
            | "defines" defines_list
            | "notes" notes_list

name_type_list: ID "::" ID
              | ID "::" ID "." ID
              | ID "::" ID "and" name_type_list

props_list_and_sep: props ("and" props)*

defines_list: defines_list_element ("and" defines_list_element)*

defines_list_element: thmdecl? (ID | QUOTED_STRING) prop_pat?

notes_list: notes_list_element ("and" notes_list_element)*

notes_list_element: thmdef? thms

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.3
#

interpretation_block : "interpretation" locale_expr proof_prove

interpret: "interpret" locale_expr

global_interpretation: "global_interpretation" locale_expr definitions?

sublocale: "sublocale" (name ("<" | "\\<subseteq>")?)? locale_expr definitions?

definitions_item: thmdecl? name mixfix? "=" term

definitions: "defines" definitions_item ("and" definitions_item)*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.9
#

consts: "consts" const_decls

const_decls: const_decl+

const_decl: name "::" type mixfix?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.8
#

instantiation : "instantiation" name_list_and_sep "::" arity "begin" local_theory "end"

name_list_and_sep : name "and" name_list_and_sep
                     | name

class_instance: "instance"
              | "instance" name_list_and_sep "::" arity
              | "instance" name "<" name
              | "instance" name "\\<subseteq>" name

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.10
#

ml : ("ml" | "setup") cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.12.2
#

typedecl : "typedecl" typespec mixfix?

type_synonym : "type_synonym" typespec "=" (ID | QUOTED_STRING) mixfix?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.13
#

lemmas : "lemmas" thmdef? thms for_fixes

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.15
#


hide_declarations : "hide_class" ("(" "open" ")")? name_list
                  | "hide_type" ("(" "open" ")")? name_list
                  | "hide_const" ("(" "open" ")")? name_list
                  | "hide_fact" ("(" "open" ")")? name_list

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.1.3
#

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.1
#

fix : "fix" vars

assume: "assume" concl (prems)? (for_fixes)?
      | "presume" concl (prems)? (for_fixes)?

concl : props ("and" props)*

# TODO should be props'_list in first line instead, but don't find
prems: "if" (props ("and" props)*)
     | "define" vars "where" props ("and" props)* for_fixes?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.2
#

let: "let" let_statement ("and" let_statement)*

let_statement: term ("and" term)* "=" term

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.3
#

proof_state: "also" proof_state
           | "done"
           | "done" local_theory
           | "done" proof_state
           | "done" theory
           | "moreover" proof_state
           | "next" proof_state
           | "oops"
           | "oops" theory
           | "then" proof_chain
           | "ultimately" proof_chain
           | "{" proof_state "}" proof_state
           | assume proof_state
           | case proof_state
           | consider proof_prove
           | doc_block proof_state
           | fix proof_state
           | from proof_chain
           | have proof_prove
           | hence proof_prove
           | interpret proof_prove
           | let proof_state
           | note proof_state
           | note proof_state
           | obtain proof_prove
           | prems proof_state
           | proof proof_state
           | qed
           | qed local_theory
           | qed proof_state
           | qed theory
           | show proof_prove
           | subgoal proof_prove
           | terminal_proof_steps
           | thus proof_prove
           | unfolding proof_prove
           | using proof_prove
           | with proof_chain

proof_state_statements : proof_state_statement
                      | proof_state_statement "and" proof_state_statements

proof_state_statement : thmdef
                     | thmdef thms

proof_chain: consider proof_prove
           | have proof_prove
           | interpret proof_prove
           | obtain proof_prove
           | show proof_prove
           | subgoal proof_prove

note: "note" (thmdef? thms) ("and" thmdef? thms)*

from: "from" thms ("and" thms)*

with: "with" thms ("and" thms)*

using: "using" thms ("and" thms)*

unfolding: "unfolding" thms ("and" thms)*

# TODO the first line is adhoc based on AFP, and doesn't match the grammar
# "class_instance proof_prove" not allowed in Isabelle/Isar grammar, but found in AFP
local_theory: goal proof_prove
            | statement local_theory
            | statement
            | declare local_theory
            | doc_block local_theory
            | class_instance local_theory
            | class_instance proof_prove

# "note" "also" proof_state here contradicts grammar in Isabelle/Isar
proof_prove : "show" stmt cond_stmt
               | "show" stmt cond_stmt for_fixes
               | "hence" stmt cond_stmt
               | "hence" stmt cond_stmt for_fixes
               | apply proof_prove
               | apply
               | supply_block proof_prove
               | supply_block
               | subgoal proof_prove
               | prefer_block proof_prove
               | prefer_block
               | "also" proof_state
               | "done" proof_state
               | "done" theory
               | "done" local_theory
               | "done"
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
               | "oops" theory
               | "oops"
               | terminal_proof_steps proof_state
               | terminal_proof_steps local_theory
               | terminal_proof_steps theory
               | terminal_proof_steps
               | doc_block proof_prove
               | termination proof_prove

# QUOTED_STRING only found in AFP, not in Isabelle/Isar grammar
conclusion : "shows" stmt
           | "obtains" obtain_clauses

obtain_clauses: obtain_case
              | par_name obtain_case
              | par_name obtain_case "|" obtain_clauses
              | obtain_case "|" obtain_clauses

obtain_case : obtain_case_statements
               | vars "where" obtain_case_statements

obtain_case_statements : obtain_case_statement
                          | obtain_case_statement "and" obtain_case_statements

obtain_case_statement : prop_list
                         | thmdecl prop_list

# no rail road diagram
assms : "assms"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.4
#

goal : "lemma" "(" "in" ID ")" long_statement
        | "lemma" "(" "in" ID ")" short_statement
        | "theorem" "(" "in" ID ")" long_statement
        | "theorem" "(" "in" ID ")" short_statement
        | "corollary" "(" "in" ID ")" long_statement
        | "corollary" "(" "in" ID ")" short_statement
        | "proposition" "(" "in" ID ")" long_statement
        | "proposition" "(" "in" ID ")" short_statement
        | "schematic_goal" "(" "in" ID ")" long_statement
        | "schematic_goal" "(" "in" ID ")" short_statement
        | "lemma" long_statement
        | "lemma" short_statement
        | "theorem" long_statement
        | "theorem" short_statement
        | "corollary" long_statement
        | "corollary" short_statement
        | "proposition" long_statement
        | "proposition" short_statement
        | "schematic_goal" long_statement
        | "schematic_goal" short_statement

have: "have" stmt cond_stmt? for_fixes?

show: "show" stmt cond_stmt? for_fixes?

hence: "hence" stmt cond_stmt? for_fixes?

thus: "thus" stmt cond_stmt? for_fixes?

stmt: props ("and" props)*

cond_stmt: ("if" | "when") stmt

short_statement: stmt ("if" stmt)? for_fixes?

long_statement: thmdecl? statement_context conclusion

statement_context: includes context_elem_list?
                 | context_elem_list

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.3
#


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.1
#

# TODO missing induct, induction, and coinduct
method: (name | ("(" methods ")")) method_modifier?
      | cases

method_modifier: "?" | "+" | "[" NAT "]"

method_name: name

methods: (method | method_name method_args?) (("," | ";" | "|") (method | method_name method_args))*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.2
#

proof: "proof" SYM_IDENT? (method | "-")?

qed: "qed" method?

by: "by" method method?

terminal_proof_steps : "." | ".." | "sorry"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.1


case : "case" (ID | "True" | "False" | NAT | "(" name_underscore_list ")")

name_underscore_list : (name | NAT | "_" )+

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.2
#

cases : "cases" no_simp_block insts_list_and_sep rule
      | "cases" no_simp_block rule
      | "cases" no_simp_block insts_list_and_sep
      | "cases" no_simp_block
      | "cases" insts_list_and_sep rule
      | "cases" insts_list_and_sep
      | "cases" QUOTED_STRING rule
      | "cases" QUOTED_STRING
      | "cases" rule
      | "cases"

insts_list_and_sep : insts "and" insts_list_and_sep
                      | insts

no_simp_block : "(" "no_simp" ")"

arbitary_block : arbitrary

arbitrary : "arbitrary" ":" term_list_and

term_list_and : term
              | term "and" term_list_and

taking: "taking" ":" insts

rule_block : rule

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.6
#

consider: "consider" obtain_clauses

obtain: "obtain" (vars "where")? (par_name)? concl (prems)? (for_fixes)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 7.1
#

apply : "apply" method
      | "apply_end" method

supply_block : "supply" proof_state_statements

prefer_block : "prefer" NAT

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.2
#

mixfix : "(" template ")"
       | "(" template prios ")"
       | "(" template NAT ")"
       | "(" template prios NAT ")"
       | "(" "infix" template NAT ")"
       | "(" "infixl" template NAT ")"
       | "(" "infixr" template NAT ")"
       | "(" "binder" template NAT ")"
       | "(" "binder" template prio NAT ")"
       | "structure"

template : QUOTED_STRING
         | cartouche

prios : "[" nat_list "]"

prio : "[" NAT "]"

nat_list : NAT
         | NAT "," nat_list

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.3
#

notation_block : "notation" notation_list
               | "notation" mode notation_list
               | "no_notation" notation_list
               | "no_notation" mode notation_list

notation_list : notation
              | notation "and" notation_list

notation : name mixfix

# TODO
mode : ID
     | "(" "input" ")"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.5.2
#

syntax : "syntax" mode constdecl_list
       | "syntax" constdecl_list
       | "no_syntax" mode constdecl_list
       | "no_syntax" constdecl_list

translations : "translations" transpat "=" "=" transpat
             | "translations" transpat "=" ">" transpat
             | "translations" transpat "<" "=" transpat
             | "translations" transpat "\\<rightleftharpoons>" ">" transpat
             | "no_translations" transpat "=" "=" transpat
             | "no_translations" transpat "=" ">" transpat
             | "no_translations" transpat "<" "=" transpat
             | "no_translations" transpat "\\<rightleftharpoons>" ">" transpat

transpat : QUOTED_STRING
         | "(" name ")" QUOTED_STRING

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 9.2.1
#

folded : "folded" thms
       | "unfolded" thms

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.1
#

inductive : "inductive" vars for_fixes "where" multi_specs "monos" thms
          | "inductive" vars for_fixes "where" multi_specs
          | "inductive" vars for_fixes "monos" thms

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2
#

primrec : "primrec" specification

fun_block : ("fun" | "function") specification proof_prove?

opts : "(" opt_list ")"

opt_list : sequential
         | domintros
         | sequential "," opt_list
         | domintros "," opt_list

termination: "termination" term?

# TODO: not spec'ed
sequential : ID
           | QUOTED_STRING

# TODO: not spec'ed
domintros : ID
          | QUOTED_STRING

# TODO generated from examples
datatype : "datatype" generic_type "=" constructors

generic_type : type name
             | type

constructors : constructor
             | constructor "|" constructors

constructor : ID TYPE_IDENT comment_block
            | ID TYPE_IDENT
            | ID ID comment_block
            | ID ID
            | ID QUOTED_STRING comment_block
            | ID QUOTED_STRING
            | ID comment_block
            | ID

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2.2
#

partial_function : "partial_function" "(" name ")" specification

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.6.2
#

record : "record" overloaded typespec_sorts "=" type "+" constdecl_list
       | "record" typespec_sorts "=" type "+" constdecl_list
       | "record" overloaded typespec_sorts "=" constdecl_list
       | "record" typespec_sorts "=" constdecl_list

constdecl_list : constdecl
               | constdecl constdecl_list

constdecl : name "::" type
          | name "::" type comment_block
          | name "::" type mixfix

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.7
#

overloaded : "(" "overloaded" ")"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 12.2
#

nitpick : "nitpick" "[" args "]" NAT
        | "nitpick" "[" args "]"
        | "nitpick" NAT
        | "nitpick"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 13
#

export_code : "open" const_expr_list export_target_list
            | const_expr_list export_target_list

const_expr_list : const_expr
                | const_expr const_expr_list

export_target_list : export_target export_target_list

export_target : "in" target "module_name" ID "file_prefix" path "(" args ")"
              | "in" target "module_name" ID "file_prefix" path
              | "in" target "module_name" ID "(" args ")"
              | "in" target "module_name" ID
              | "in" target "file_prefix" path "(" args ")"
              | "in" target "file_prefix" path
              | "in" target "(" args ")"
              | "in" target

target : "SML"
       | "OCaml"
       | "Haskell"
       | "Scala"
       | "Eval"


#
# Not covered the grammar
#

derive: "derive" "(" ID ")" ID*

const_expr : const
           | ID "." "_"
           | "_"

const : term

path : embedded
"""

# Define precedence and associativity (optional for Isabelle)
precedence = ()


# Build the parser
parser = Lark(grammar, start='start', parser='earley')


def parse(input_text):
    try:
        tree = parser.parse(input_text)
        return tree
    except Exception as e:
        print(f"Error parsing input: {e}")
