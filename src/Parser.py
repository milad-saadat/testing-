from lark import Lark
import lark
from src.Polynomial import Polynomial
from src.Polynomial import Monomial
from src.Coefficient import Coefficient
from src.Coefficient import Element
from src.UnknownVariable import UnknownVariable
from src.Constraint import PolynomialConstraint


# def find_variable(parse_tree):
#     return UnknownVariable.get_variable_by_name(name=parse_tree)


# class SetOfVariables:
#     program_declared_var = []
#     all_declared_var = []
#     template_declared_var = []


#
# def find_index_of_variable(name):
#     var = UnknownVariable.get_variable_by_name(name)
#     for i in range(len(SetOfVariables.program_declared_var)):
#         if var == SetOfVariables.program_declared_var[i]:
#             return i
#     print(f'no such var declared with name : {name}')
#     return None
#
#
# def traverse(parse_tree):
#     if parse_tree.__class__ is lark.Token:
#         return find_variable(parse_tree)
#
#     if parse_tree.data == 'start':
#         return traverse(parse_tree.children[0])
#     elif parse_tree.data == 'polynomial':
#         if parse_tree.children[0].data == 'monomial':
#             return Polynomial(SetOfVariables.program_declared_var, [traverse(parse_tree.children[0])])
#         poly = Polynomial(SetOfVariables.program_declared_var, [])
#         for child in parse_tree.children:
#             poly = poly + traverse(child)
#         return poly.revise()
#
#     elif parse_tree.data == 'coefficient':
#         if parse_tree.children[0].data == 'element':
#             return Coefficient([traverse(parse_tree.children[0])])
#         coef = Coefficient([])
#         for child in parse_tree.children:
#             coef = coef + traverse(child)
#         return coef.revise()
#
#     elif parse_tree.data == 'element':
#         variables = []
#         start = 0
#         constant = 1
#         if parse_tree.children[0].type == 'RATIONALNUMBER':
#             constant = parse_tree.children[0]
#             start = 1
#         for i in range(start, len(parse_tree.children)):
#             variables.append(traverse(parse_tree.children[i]))
#         return Element(constant, variables)
#
#     elif parse_tree.data == 'monomial':
#         if parse_tree.children[0].__class__ is lark.Token:
#             if parse_tree.children[0].type == 'RATIONALNUMBER':
#                 coefficient = Coefficient([Element(str(parse_tree.children[0]), [])])
#             else:
#                 coefficient = Coefficient(
#                     [Element('1', [UnknownVariable.get_variable_by_name(parse_tree.children[0])])])
#         else:
#             coefficient = traverse(parse_tree.children[0])
#         variables = SetOfVariables.program_declared_var
#         degrees = [0] * len(SetOfVariables.program_declared_var)
#         for i in range(1, len(parse_tree.children), 2):
#             index = find_index_of_variable(parse_tree.children[i])
#             degrees[index] = (int(parse_tree.children[i + 1]))
#         return Monomial(variables, degrees, coefficient)
#
#     elif parse_tree.data == 'constraint':
#         poly = traverse(parse_tree.children[0])
#         return PolynomialConstraint(poly, str(parse_tree.children[1]))
#
#     elif parse_tree.data == 'template_var_declare':
#         SetOfVariables.template_declared_var = traverse(parse_tree.children[0])
#
#     elif parse_tree.data == 'program_var_declare':
#         SetOfVariables.program_declared_var = traverse(parse_tree.children[0])
#
#     elif parse_tree.data == 'set_of_var':
#         new_declared_var = []
#         for child in parse_tree.children:
#             new_unknown_variable = UnknownVariable(name=str(child))
#             new_declared_var.append(new_unknown_variable)
#             SetOfVariables.all_declared_var.append(new_unknown_variable)
#         return new_declared_var
#
#
# def convert_string_to_polynomial(poly_text):
#     parser = Lark(r"""
#             start : polynomial
#
#             element : (RATIONALNUMBER | VAR) ("*" VAR) *
#             coefficient: element | "(" coefficient ")" | coefficient "+" coefficient
#             monomial :  ("(" coefficient ")" | RATIONALNUMBER | VAR ) ("*" VAR "^" NUMBER)*
#             polynomial : polynomial "+" polynomial  | monomial
#
#             VAR: /\w/+
#             RATIONALNUMBER : /[+-]?/ NUMBER ("/" NUMBER)?
#
#
#             %import common.NUMBER
#             %import common.NEWLINE -> _NL
#             %import common.WS_INLINE
#             %ignore WS_INLINE
#         """, parser="lalr")
#
#     parse_tree = parser.parse(poly_text)
#     return traverse(parse_tree)
#
#
# def convert_string_to_constraint(cons_text):
#     parser = Lark(r"""
#             start : constraint
#
#             element : (RATIONALNUMBER | VAR) ("*" VAR) *
#             coefficient: element | "(" coefficient ")" | coefficient "+" coefficient
#             monomial :  ("(" coefficient ")" | RATIONALNUMBER | VAR ) ("*" VAR "^" NUMBER)*
#             polynomial : polynomial "+" polynomial  | monomial
#             constraint : polynomial SIGN "0"
#
#             SIGN : ">" | ">=" | "=" | "<" | "<="
#             VAR: /\w/+
#             RATIONALNUMBER : /[+-]?/ NUMBER ("/" NUMBER)?
#
#
#             %import common.NUMBER
#             %import common.NEWLINE -> _NL
#             %import common.WS_INLINE
#             %ignore WS_INLINE
#         """, parser="lalr")
#
#     parse_tree = parser.parse(cons_text)
#     return traverse(parse_tree)
#
#
# def convert_string_to_set_of_variables(cons_text):
#
#     parser = Lark(r"""
#             start : template_var_declare | program_var_declare
#
#             template_var_declare : "declare template vars" set_of_var
#             program_var_declare : "declare program vars" set_of_var
#             set_of_var : (VAR)*
#
#             SIGN : ">" | ">=" | "="
#             VAR: /\w/+
#             RATIONALNUMBER : /[+-]?/ NUMBER
#
#             %import common.NUMBER
#             %import common.NEWLINE -> _NL
#             %import common.WS_INLINE
#             %ignore WS_INLINE
#         """, parser="lalr")
#
#     parse_tree = parser.parse(cons_text)
#     traverse(parse_tree)
