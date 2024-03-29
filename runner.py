import json
import sys

from src.PositiveModel import *

with open(sys.argv[3], "r") as jsonfile:
    data = json.load(jsonfile)

sat_heuristic = False
if 'SAT_heuristic' in data.keys():
    sat_heuristic = data['SAT_heuristic']

degree_of_sat = 0
if 'degree_of_sat' in data.keys():
    degree_of_sat = data['degree_of_sat']

degree_of_nonstrict_unsat = 0
if 'degree_of_nonstrict_unsat' in data.keys():
    degree_of_nonstrict_unsat = data['degree_of_nonstrict_unsat']


degree_of_strict_unsat = 0
if 'degree_of_strict_unsat' in data.keys():
    degree_of_strict_unsat = data['degree_of_strict_unsat']

max_d_of_strict = 0
if 'max_d_of_strict' in data.keys():
    max_d_of_strict = data['max_d_of_strict']

unsat_core_heuristic = False
if 'unsat_core_heuristic' in data.keys():
    unsat_core_heuristic = data['unsat_core_heuristic']

global model
model = PositiveModel([],
                      data['theorem_name'],
                      True, not sat_heuristic, not sat_heuristic,
                      degree_of_sat, degree_of_nonstrict_unsat, degree_of_strict_unsat,
                      max_d_of_strict
                      )

def traverse_readable_tree(parse_tree):
    if parse_tree.data == 'start':
        for child in parse_tree.children:
            traverse_readable_tree(child)
    elif parse_tree.data == 'program_var':
        for child in parse_tree.children:
            model.program_variables.append(UnknownVariable(str(child), type_of_var='program_var'))

    elif parse_tree.data == 'template_var':
        for child in parse_tree.children:
            model.template_variables.append(UnknownVariable(str(child), type_of_var='template_var'))

    elif parse_tree.data == 'hornclause':
        lhs = traverse_readable_tree(parse_tree.children[0])
        rhs = traverse_readable_tree(parse_tree.children[1])
        model.add_paired_constraint(lhs, rhs)
        return
    elif parse_tree.data == 'precondition':
        dnf = traverse_readable_tree(parse_tree.children[0])
        model.preconditions.append(dnf)
        return
    elif parse_tree.data == 'dnf':
        if len(parse_tree.children) == 1:
            return traverse_readable_tree(parse_tree.children[0])
        else:
            if str(parse_tree.children[1]) == "AND":
                return (traverse_readable_tree(parse_tree.children[0]) & traverse_readable_tree(parse_tree.children[2]))
            else:
                return (traverse_readable_tree(parse_tree.children[0]) | traverse_readable_tree(parse_tree.children[2]))

    elif parse_tree.data == 'literal':
        literal = []
        for i in range(len(parse_tree.children)):
            literal.append(traverse_readable_tree(parse_tree.children[i]))
        return literal
    elif parse_tree.data == 'constraint':
        return DNF([[PolynomialConstraint(traverse_readable_tree(parse_tree.children[0]) - traverse_readable_tree(parse_tree.children[2]), str(parse_tree.children[1]))]])
    elif parse_tree.data == 'polynomial':
        return convert_to_desired_poly(traverse_readable_tree(parse_tree.children[0]), model.program_variables)
    elif parse_tree.data == 'expression':
        if len(parse_tree.children) == 1:
            return traverse_readable_tree(parse_tree.children[0])
        elif parse_tree.children[1] == '+':
             return traverse_readable_tree(parse_tree.children[0]) + traverse_readable_tree(parse_tree.children[2])
        elif parse_tree.children[1] == '-':
            return traverse_readable_tree(parse_tree.children[0]) - traverse_readable_tree(parse_tree.children[2])

    elif parse_tree.data == 'term':
        if len(parse_tree.children) == 1:
            return traverse_readable_tree(parse_tree.children[0])
        else:
            return traverse_readable_tree(parse_tree.children[0]) * traverse_readable_tree(parse_tree.children[1])

    elif parse_tree.data == 'factor':
        if len(parse_tree.children) == 1:
            return traverse_readable_tree(parse_tree.children[0])
        elif parse_tree.children[0] == '-':
            return -traverse_readable_tree(parse_tree.children[1])
        elif parse_tree.children[0] == '+':
            return traverse_readable_tree(parse_tree.children[1])

    elif parse_tree.data == 'primary':
        if not parse_tree.children[0].__class__ is lark.Token:
            return traverse_readable_tree(parse_tree.children[0])
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
            start : program_var template_var precondition* hornclause*
            
            program_var : "Program_var:" VAR* ";"
            
            template_var : "Template_var:" VAR* ";"
            
            precondition : "Precondition:" dnf
            
            hornclause : "Horn_clause:" dnf "->" dnf
            
            dnf : constraint | "(" dnf ")" | dnf LOGICAL_SIGN dnf
             
            
            constraint : polynomial COMP_SIGN polynomial 
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
    return traverse_readable_tree(parse_tree)


def traverse_smt_tree(parse_tree):
    if parse_tree.data == 'start':
        for child in parse_tree.children:
            traverse_smt_tree(child)

    elif parse_tree.data == 'instructions':
        return
    elif parse_tree.data == 'declare_var':
        model.template_variables.append(UnknownVariable(str(parse_tree.children[0]), type_of_var='template_var'))

    elif parse_tree.data == 'assertion':
        traverse_smt_tree(parse_tree.children[0])
    elif parse_tree.data == 'hornclause':
        model.program_variables = []
        for i in range(len(parse_tree.children)-2):
            traverse_smt_tree(parse_tree.children[i])
        lhs = traverse_smt_tree(parse_tree.children[-2])
        rhs = traverse_smt_tree(parse_tree.children[-1])
        model.add_paired_constraint(lhs, rhs, model.program_variables)
        return
    elif parse_tree.data == 'program_variables':
        model.program_variables.append(UnknownVariable(str(parse_tree.children[0]), type_of_var='program_var'))
    elif parse_tree.data == 'precondition':
        dnf = traverse_smt_tree(parse_tree.children[0])
        if len(parse_tree.children) == 2:
            second_dnf = traverse_smt_tree(parse_tree.children[1])
            model.preconditions.append((dnf, second_dnf))
        else:
            model.preconditions.append((dnf, ))
        return
    elif parse_tree.data == 'dnf':
        if len(parse_tree.children) == 1:
            return traverse_smt_tree(parse_tree.children[0])
        else:
            if str(parse_tree.children[0]) == "and":
                result_dnf = DNF([])
                for i in range(1, len(parse_tree.children)):
                    result_dnf = result_dnf & traverse_smt_tree(parse_tree.children[i])
                return result_dnf
            else:
                result_dnf = DNF([])
                for i in range(1, len(parse_tree.children)):
                    result_dnf = result_dnf | traverse_smt_tree(parse_tree.children[i])
                return result_dnf

    elif parse_tree.data == 'constraint':
        return DNF(
            [[
                PolynomialConstraint(
                    traverse_smt_tree(parse_tree.children[1] )
                    -
                    traverse_smt_tree(parse_tree.children[2]),
                                      str(parse_tree.children[0]))]])
    elif parse_tree.data == 'polynomial':
        return convert_to_desired_poly(traverse_smt_tree(parse_tree.children[0]), model.program_variables)
    elif parse_tree.data == 'expression':

        if len(parse_tree.children) == 1:
            if parse_tree.children[0].data == "fraction":
                return Solver.get_constant_polynomial(model.template_variables + model.program_variables,
                                                      traverse_smt_tree(parse_tree.children[0])
                                                      )
            return traverse_smt_tree(parse_tree.children[0])
        elif len(parse_tree.children) == 2:
            if str(parse_tree.children[0]) == '+':
                return traverse_smt_tree(parse_tree.children[1])
            elif str(parse_tree.children[0]) == '-':
                return -traverse_smt_tree(parse_tree.children[1])
        elif len(parse_tree.children) == 3:

            if str(parse_tree.children[0]) == '+':
                return traverse_smt_tree(parse_tree.children[1]) + traverse_smt_tree(parse_tree.children[2])
            elif str(parse_tree.children[0]) == '-':
                return traverse_smt_tree(parse_tree.children[1]) - traverse_smt_tree(parse_tree.children[2])
            elif str(parse_tree.children[0]) == '*':
                return traverse_smt_tree(parse_tree.children[1]) * traverse_smt_tree(parse_tree.children[2])
        else:
            poly = traverse_smt_tree(parse_tree.children[1])
            for i in range(2, len(parse_tree.children)):
                if str(parse_tree.children[0]) == '+':
                    poly = poly + traverse_smt_tree(parse_tree.children[i])
                else:
                    poly = poly * traverse_smt_tree(parse_tree.children[i])
            return poly
    elif parse_tree.data == 'primary':
        if type(parse_tree.children[0]) is lark.tree.Tree:
            return Solver.get_constant_polynomial(model.template_variables + model.program_variables,
                                                   traverse_smt_tree(parse_tree.children[0]))

        if parse_tree.children[0].type == 'VAR':
            deg = 1
            if len(parse_tree.children) > 1:
                deg = int(parse_tree.children[1])
            degrees = [0] * len(model.template_variables + model.program_variables)
            degrees[find_index_of_variable(str(parse_tree.children[0]),
                                           model.template_variables + model.program_variables)] = deg
            return Solver.get_degree_polynomial(model.template_variables + model.program_variables, degrees)

    elif parse_tree.data == 'fraction':
        return str(traverse_smt_tree(parse_tree.children[0])) + '/' + str(traverse_smt_tree(parse_tree.children[1]))
    elif parse_tree.data == 'rationalnumber':
        if len(parse_tree.children) == 1:
            return str(parse_tree.children[0])
        if len(parse_tree.children) == 2:
            return str(parse_tree.children[0]) + str(parse_tree.children[1])

def parse_smt_file(poly_text: str):
    parser = Lark(r"""
            start : declare_var* assertion* instructions* 
            
            instructions: "(check-sat)" | "(get-model)"
            declare_var: "(declare-const" VAR VAR_TYPE ")"
            
            assertion: "(assert" precondition  ")" | "(assert" hornclause  ")"
            precondition : dnf | "(=>" dnf dnf ")" 

            hornclause : "(forall" "(" program_variables* ")" "(=>" dnf dnf ")" ")"
            program_variables : "(" VAR VAR_TYPE ")" 
            dnf : constraint | "(" LOGICAL_SIGN dnf+ ")" 


            constraint : "(" COMP_SIGN polynomial polynomial ")" 
            polynomial : expression
            expression : "(/" fraction ")" | primary | "(" SIGN expression ")" | "(" SIGN expression+ ")"

            primary : VAR | rationalnumber 
            
            LOGICAL_SIGN : "and" | "or" 
            COMP_SIGN : ">" | "=" | "<" | ">=" | "<="
            SIGN : "+" | "-" | "*"
            VAR: /[a-zA-Z0-9_]/+
            VAR_TYPE: "Int" | "Real" 
            rationalnumber : NUMBER | "(" SIGN NUMBER ")" | SIGN NUMBER 
            fraction: rationalnumber  rationalnumber 

            %import common.NUMBER
            %import common.NEWLINE -> _NL
            %import common.WS_INLINE
            %import common.WS
            %ignore WS
        """, parser="lalr")

    parse_tree = parser.parse(poly_text)
    return traverse_smt_tree(parse_tree)

with open(sys.argv[2], "r") as file:
    file_input = file.read()

if sys.argv[1] == "-smt":
    parse_smt_file(file_input)
elif sys.argv[1] == "-H":
    parse_readable_file(file_input)
else:
    print("not defined format")
    exit(0)

model.run_on_solver(temp_path=data["temp_path"], solver_name=data["solver_name"], solver_path=data["solver_path"],
                    core_iteration_heuristic=unsat_core_heuristic,
                    constant_heuristic=False,
                    real_values=data["real_values"]
                    )
