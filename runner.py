import json

from src.Polynomial import Polynomial
from lark import Lark
import lark
from src.UnknownVariable import UnknownVariable
from src.Solver import Solver
from src.Polynomial import Monomial
from src.Convertor import *
from src.PositiveModel import *

program_vars = []
template_vars = []


def traverse(parse_tree):
    if parse_tree.data == 'start':
        for child in parse_tree.children:
            traverse(child)
    elif parse_tree.data == 'program_var':
        for child in parse_tree.children:
            program_vars.append(str(child))
    elif parse_tree.data == 'template_var':
        for child in parse_tree.children:
            template_vars.append(str(child))
        global model
        model = PositiveModel(template_vars, program_vars,
                              data['model_name'],
                              data['get_SAT'], data['get_UNSAT'], data['get_strict'],
                              data['max_d_of_SAT'], data['max_d_of_UNSAT'], data['max_d_of_strict'],
                              data['degree_of_generated_var']
                              )

    elif parse_tree.data == 'horncaluse':
        lhs = traverse(parse_tree.children[0])
        rhs = traverse(parse_tree.children[1])
        print(lhs)
        print(rhs)
        model.add_paired_constraint(lhs, rhs)
        return
    elif parse_tree.data == 'precondition':
        dnf = traverse(parse_tree.children[0])
        print(dnf)
        model.preconditions.append(dnf)
        return
    elif parse_tree.data == 'dnf':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0])
        else:
            if str(parse_tree.children[1]) == "AND":
                return (traverse(parse_tree.children[0]) & traverse(parse_tree.children[2]))
            else:
                return (traverse(parse_tree.children[0]) | traverse(parse_tree.children[2]))

    elif parse_tree.data == 'literal':
        literal = []
        for i in range(len(parse_tree.children)):
            literal.append(traverse(parse_tree.children[i]))
        return literal
    elif parse_tree.data == 'constraint':
        return DNF([[PolynomialConstraint(traverse(parse_tree.children[0]), str(parse_tree.children[1]))]])
    elif parse_tree.data == 'polynomial':
        return convert_to_desired_poly(traverse(parse_tree.children[0]), model.program_variables)
    elif parse_tree.data == 'expression':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0])
        elif parse_tree.children[1] == '+':
             return traverse(parse_tree.children[0]) + traverse(parse_tree.children[2])
        elif parse_tree.children[1] == '-':
            return traverse(parse_tree.children[0]) - traverse(parse_tree.children[2])

    elif parse_tree.data == 'term':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0])
        else:
            return traverse(parse_tree.children[0]) * traverse(parse_tree.children[1])

    elif parse_tree.data == 'factor':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0])
        elif parse_tree.children[0] == '-':
            return -traverse(parse_tree.children[1])
        elif parse_tree.children[0] == '+':
            return traverse(parse_tree.children[1])

    elif parse_tree.data == 'primary':
        if not parse_tree.children[0].__class__ is lark.Token:
            return traverse(parse_tree.children[0])
        elif parse_tree.children[0].type == 'RATIONALNUMBER':
            return Solver.get_constant_polynomial(model.template_variables + model.program_variables,
                                                  str(parse_tree.children[0]))
        else:
            deg = 1
            if len(parse_tree.children) > 1:
                deg = int(parse_tree.children[1])
            degrees = [0] * len(model.template_variables + model.program_variables)
            degrees[find_index_of_variable(str(parse_tree.children[0]),
                                           model.template_variables + model.program_variables)] = deg
            return Solver.get_degree_polynomial(model.template_variables + model.program_variables, degrees)


def parse_readable_file(poly_text: str):
    parser = Lark(r"""
            start : program_var template_var precondition* horncaluse*
            
            program_var : "Program_var:" VAR* ";"
            
            template_var : "Template_var:" VAR* ";"
            
            precondition : "Precondition:" dnf
            
            horncaluse : "Horn_clause:" dnf "->" dnf
            
            dnf : constraint | "(" dnf ")" | dnf LOGICAL_SIGN dnf
             
            
            constraint : polynomial COMP_SIGN "0" 
            polynomial : expression
            expression : term | expression SIGN term 

            term : factor | term "*" factor

            factor : primary | SIGN factor

            primary : VAR | RATIONALNUMBER | VAR "^" RATIONALNUMBER  | "(" expression ")"
            
            LOGICAL_SIGN : "AND" | "OR" 
            COMP_SIGN : ">" | "=" | "<" | ">=" | "<="
            SIGN : "+" | "-" 
            VAR: /[a-zA-Z0-9_]/+
            RATIONALNUMBER : /[+-]?/ NUMBER ("/" NUMBER)?


            %import common.NUMBER
            %import common.NEWLINE -> _NL
            %import common.WS_INLINE
            %import common.WS
            %ignore WS
        """, parser="lalr")

    parse_tree = parser.parse(poly_text)
    print(parse_tree.pretty())
    return traverse(parse_tree)


with open("./config", "r") as jsonfile:
    data = json.load(jsonfile)

with open("./test.txt", "r") as file:
    file_input = file.read()
parse_readable_file(file_input)

model.run_on_solver(temp_path=data["temp_path"], solver_name=data["solver_name"], solver_path=data["solver_path"],
                    core_iteration_heuristic=data["core_iteration_heuristic"],
                    constant_heuristic=data["constant_heuristic"],
                    real_values=data["real_values"]
                    )
