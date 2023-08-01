from src.UnknownVariable import UnknownVariable
from src.Coefficient import Element
from src.Coefficient import Coefficient
from src.Polynomial import Monomial
from src.Polynomial import Polynomial
import numpy as np
from src.Parser import *
from src.Constraint import *
from src.Solver import *
from src.Farkas import Farkas
from src.Handelman import Handelman
from src.Putinar import Putinar
from src.Constraint import CoefficientConstraint
import os
from src.Convertor import *
import subprocess
from src.Model import *
from src.gurobi import *


if __name__ == '__main__':
    # a = UnknownVariable('a')
    # b = UnknownVariable('b')
    # c = UnknownVariable('c')
    # x = UnknownVariable('x')
    # y = UnknownVariable('y')
    # #
    # element1 = Element(constant='7/10', variables=[a])
    # element2 = Element('1.3', [a, b])
    # element3 = Element('2', [a])
    # element4 = Element('3', [])
    #
    # coef1 = Coefficient([element3, element2])
    # cons1 = CoefficientConstraint(coef1, '=')
    # print(cons1)
    # coef2 = Coefficient([element3, element4])
    # cons2 = CoefficientConstraint(coef2, '=')
    # print(cons2)
    # Solver.remove_equality_constraints([cons1, cons2])
    #
    # print(coef1 - coef2)

    # mono1 = Monomial([x,y], [1,2], coef1)
    # print(mono1)
    #
    # mono2 = Monomial([x,y], [3,0], coef2)
    # print(mono2)
    #
    # mono3 = Monomial([x,y], [0,1], coef1)
    #
    # mono4 = Monomial([x,y], [2,4], coef1+coef2)
    #
    # poly1 = Polynomial([x,y], [mono1, mono2])
    # poly2 = Polynomial([x,y], [mono1, mono3])
    #
    # print(poly1)
    # print(poly2)
    # print(poly1 * poly2)
    # poly1 = (convert_string_to_polynomial('(5.5*a*a)*x^2*y^0 + (2*b)*x^0*y^0'))
    # poly2 = convert_string_to_polynomial('(-1.2*b)*x^0*y^2 + (3*a + -1)*x^0*y^0')
    # print(poly1)
    # print(poly2)
    # print(poly1-poly2)
    # const = PolynomialConstraint(poly2, ">=")
    # print(const.is_strict())
    # variables = [x, y]
    # xxx = Polynomial(variables, [Monomial(variables, [0]*len(variables), Coefficient([Element(1, [UnknownVariable('lambda1')])]))])
    # yyy = Polynomial(variables, [Monomial(variables, [0]*len(variables), Coefficient([Element(1, [UnknownVariable('lambda2')])]))])
    # print(xxx * poly1 + yyy * poly2)
    # print(Solver.find_equality_constrain(poly1, poly2))
    # p1 = Polynomial(variables, [Monomial(variables, [0]*len(variables), Coefficient([Element(1, [UnknownVariable('lambda')])))])
    # print(p1)
    # print(Solver.get_variable_polynomial(variables, 'salam'))
    # print(Solver.get_constant_polynomial(variables,'2.3'))
    # poly1 = convert_string_to_polynomial('(1*c1)*i^1*j^0*ip^0*jp^0 + (1*c2)*i^0*j^1*ip^0*jp^0 + (1*d)*i^0*j^0*ip^0*jp^0')
    # poly2 = convert_string_to_polynomial('(1)*i^1*j^0*ip^0*jp^0 + (-1)*i^0*j^0*ip^1*jp^0 + (4)*i^0*j^0*ip^0*jp^0')
    # poly3 = convert_string_to_polynomial('(1)*i^0*j^1*ip^0*jp^0 + (-1)*i^0*j^0*ip^0*jp^1')
    # poly4 = convert_string_to_polynomial('(1*c1)*i^0*j^0*ip^1*jp^0 + (1*c2)*i^0*j^0*ip^0*jp^1 + (1*d)*i^0*j^0*ip^0*jp^0')
    #
    # # print(poly1)
    # # print(poly2)
    # # print(poly3)
    # # print(poly4)
    #
    # constraint1 = PolynomialConstraint(poly1, '>=')
    # constraint2 = PolynomialConstraint(poly2, '>')
    # constraint3 = PolynomialConstraint(poly3, '>')
    # constraint4 = PolynomialConstraint(poly4, '>=')
    # frakas = Farkas([constraint1, constraint2, constraint3], constraint4)
    # all_constraint = frakas.get_UNSAT_constraint(True)
    # for con in all_constraint:
    #     print(con)

    # poly1 = convert_string_to_polynomial(
    #     '(1*c1)*x^1*y^0')
    # poly2 = convert_string_to_polynomial(
    #     '(1*c2)*x^0*y^1')
    #  poly3 = convert_string_to_polynomial(
    #      '(1*c3)*x^1*y^1 + (1*c4)*x^0*y^0')
    #
    # constraint1 = PolynomialConstraint(poly1, '>')
    # constraint2 = PolynomialConstraint(poly2, '>=')
    # constraint3 = PolynomialConstraint(poly3, '>')

    # putinar = Putinar([x, y], [constraint1, constraint2], constraint3)
    #
    # all_con = putinar.get_SAT_constraint(1)
    # print(len(all_con))
    # for con in all_con:
    #     print(con)
    # all_constraint = handelman.get_SAT_constraint(2)
    # for con in all_constraint:
    #     print(con)
    # convert_string_to_set_of_variables('declare template vars c3 c2 c_1 d')
    # convert_string_to_set_of_variables('declare program vars x y ')
    # # print(convert_string_to_constraint('(5/10 *c1)*x^1 = 0').polynomial)
    # # print(convert_string_to_polynomial('(1*c3)*x^1*y^1 + (1*c4)'))
    #
    # print(convert_general_string_to_poly('(1-x+x)*(c_1+x)', SetOfVariables.all_declared_var, SetOfVariables.program_declared_var))
    # convert_string_to_set_of_variables('declare template vars c_0 c_1 c_2 c_3 s_0 s_1')
    # convert_string_to_set_of_variables('declare program vars x')
    # # # First example of first article
    # #
    # poly1 = convert_general_string_to_poly('0 -  1  +  1 * x ', SetOfVariables.all_declared_var, SetOfVariables.program_declared_var)
    # poly2 = convert_general_string_to_poly('0 -  1  +  1 * x ', SetOfVariables.all_declared_var, SetOfVariables.program_declared_var)
    # poly3 = convert_general_string_to_poly('0 -  1  +  1 * x ', SetOfVariables.all_declared_var, SetOfVariables.program_declared_var)
    # poly4 = convert_general_string_to_poly('1 * c_0  +  1 * c_1 * x', SetOfVariables.all_declared_var, SetOfVariables.program_declared_var)
    #
    # constraint1 = PolynomialConstraint(poly1, '>=')
    # constraint2 = PolynomialConstraint(poly2, '>=')
    # constraint3 = PolynomialConstraint(poly3, '>=')
    # constraint4 = PolynomialConstraint(poly4, '>=')
    # # # #
    # putinar = Putinar(constraint1.polynomial.variables, [constraint1], constraint4)
    # all_constraint = putinar.get_SAT_constraint(1)
    # # # for con in all_constraint:
    # # #     print(con)
    # print(Solver.smt_declare_variable_phase(all_constraint) + '\n' +
    #       Solver.convert_constraints_to_smt_format(all_constraint) + '\n (check-sat)\n(get-model)')
    # f = open("checking.txt", "w")
    # f.write(Solver.smt_declare_variable_phase(all_constraint) + '\n' +
    #         Solver.convert_constraints_to_smt_format(all_constraint) + '\n (check-sat)\n(get-model)')
    # f.close()
    # # os.system('./solver/z3 checking.txt')
    # output = subprocess.getoutput("./solver/z3 checking.txt")
    # print('salam ' + output)
    # Solver.core_iteration(all_constraint)
    # convert_string_to_set_of_variables('declare program vars x y')
    # print(convert_general_string_to_poly('x+--+y' , SetOfVariables.all_declared_var, SetOfVariables.program_declared_var))
    model = Model(['c_0', 'c_1', 'c_2', 'c_3', 's_0', 's_1', 's_2', 's_3'], ['x'])


    f = open("test.txt", "r")
    input = f.read().split('\n')
    i = 0
    all_constraint = []
    while i < len(input):
        i += 1
        j = i
        while i < len(input) and input[i][0] == 'd':
            i += 1
        lhs = []
        for k in range(j, i):
            lhs.append(PolynomialConstraint(
                convert_general_string_to_poly(
                    (input[k][input[k].find(':') + 1:]),
                    model.template_variables + model.program_variables,
                    model.program_variables
                )
                , '>=')
            )
        i += 1
        rhs = PolynomialConstraint(
            convert_general_string_to_poly(
                (input[i]),
                model.template_variables + model.program_variables,
                model.program_variables
            )
            , '>=')
        i += 2
        model.add_paired_constraint(lhs, rhs)


    # conss = model.get_constraints('farkas')[0]
    # for con in conss:
    #     print(con)
    #
    # print('--------------------')
    # check_constraints(conss)
    # # print(model.get_constraints('farkas'))

    model.run_on_solver(model_name='farkas', solver_name='mathsat', real_values=False)