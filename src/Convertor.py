from src.Polynomial import Polynomial
from lark import Lark
import lark
from src.UnknownVariable import UnknownVariable
from src.Solver import Solver
from src.Polynomial import Monomial


def find_index_of_variable(name, all_variable):
    var = UnknownVariable.get_variable_by_name(name)
    for i in range(len(all_variable)):
        if var == all_variable[i]:
            return i
    print(f'no such var declared with name : {name}')
    return None


def traverse(parse_tree, all_variables):
    if parse_tree.data == 'start':
        return traverse(parse_tree.children[0], all_variables)
    elif parse_tree.data == 'expression':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0], all_variables)
        elif parse_tree.children[1] == '+':
            return traverse(parse_tree.children[0], all_variables) + traverse(parse_tree.children[2], all_variables)
        elif parse_tree.children[1] == '-':
            return traverse(parse_tree.children[0], all_variables) - traverse(parse_tree.children[2], all_variables)
        else:
            print("not defined")
            return None
    elif parse_tree.data == 'term':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0], all_variables)
        else:
            return traverse(parse_tree.children[0], all_variables) * traverse(parse_tree.children[1], all_variables)

    elif parse_tree.data == 'factor':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0], all_variables)
        elif parse_tree.children[0] == '-':
            return - traverse(parse_tree.children[1], all_variables)
    elif parse_tree.data == 'primary':
        if not parse_tree.children[0].__class__ is lark.Token:
            return traverse(parse_tree.children[0], all_variables)
        elif parse_tree.children[0].type == 'RATIONALNUMBER':
            return Solver.get_constant_polynomial(all_variables, str(parse_tree.children[0]))
        else:
            deg = 1
            if len(parse_tree.children) > 1:
                deg = int(parse_tree.children[1])
            degrees = [0] * len(all_variables)
            degrees[find_index_of_variable(str(parse_tree.children[0]), all_variables)] = deg
            return Solver.get_degree_polynomial(all_variables, degrees)


def convert_to_desired_poly(poly: Polynomial, program_variables: [UnknownVariable]):
    monomials = []
    for monomial in poly.monomials:
        coef = monomial.coefficient
        degrees = [0] * len(program_variables)
        for i, var in enumerate(monomial.variables):
            if var in program_variables:
                degrees[find_index_of_variable(var.name, program_variables)] = monomial.degrees[i]
            else:
                for _ in range(monomial.degrees[i]):
                    coef.elements[0].variables.append(var)
        monomials.append(Monomial(program_variables, degrees, coef))
    return Polynomial(program_variables, monomials).revise()


def convert_general_string_to_poly(poly_text, all_variables, program_variables):
    parser = Lark(r"""
            start : expression

            expression : term | expression SIGN term 

            term : factor | term "*" factor

            factor : primary | SIGN factor

            primary : VAR | RATIONALNUMBER | VAR "^" RATIONALNUMBER  | "(" expression ")"
            
            SIGN : "+" | "-" 
            VAR: /\w/+
            RATIONALNUMBER : /[+-]?/ NUMBER ("/" NUMBER)?


            %import common.NUMBER
            %import common.NEWLINE -> _NL
            %import common.WS_INLINE
            %ignore WS_INLINE
        """, parser="lalr")

    parse_tree = parser.parse(poly_text)
    # print(parse_tree.pretty())
    return convert_to_desired_poly(traverse(parse_tree, all_variables), program_variables)
