import json
import time
import signal
import sys
import multiprocessing
from os import listdir
from os.path import isfile, join
from src.PositiveModel import *
from src.DNF import *
import pandas as pd


def handler(signum, frame):
    print("Forever is over!")
    raise Exception("end of time")


def run_on_file(file_path: str, solver_name: str):
    f = open(file_path, "r")
    file_input = f.read().split('\n')
    model = PositiveModel(file_input[1][file_input[1].find(':') + 1:-2].split(),
                          file_input[0][file_input[0].find(':') + 1:-2].split(), model_name='putinar',
                          get_UNSAT=False, get_strict=False,
                          max_d_of_SAT=2, max_d_of_UNSAT=2, max_d_of_strict=2, degree_of_generated_var=2)
    i = 4
    while i < len(file_input):

        while len(file_input[i]) == 0:
            i += 1
        i += 1
        while len(file_input[i]) == 0:
            i += 1
        j = i
        while i < len(file_input) and file_input[i][0] == 'd':
            i += 1
        lhs = []
        for k in range(j, i):
            lhs.append(PolynomialConstraint(
                model.get_polynomial(
                    (file_input[k][file_input[k].find(':') + 1:])
                )
                , '>=')
            )
        i += 1

        rhs = PolynomialConstraint(
            model.get_polynomial(
                (file_input[i])
            )
            , '>=')

        i += 3
        model.add_paired_constraint(DNF([lhs]), DNF([[rhs]]))

    start = time.time() * 1000
    is_sat, values = model.run_on_solver(solver_name=solver_name, real_values=False, constant_heuristic=False,
                                         core_iteration_heuristic=False)

    end = time.time() * 1000
    print(is_sat, end - start)
    with open("./result_" + sys.argv[2] + "_" + sys.argv[1], "w") as fp:
        fp.write(str(end - start) + "\n" + str(is_sat) + '\n')
        for var in values.keys():
            fp.write(str(var) + " : " + str(values[var]) + "\n")
    return is_sat, end - start


"""
horn_clause: 1 * x >= 0 AND 64  -  1 * x >=0 AND
 1 * tx >= 0 AND
 64  -  1 * tx >= 0 AND
 1 * y >= 0 AND
 64  -  1 * y >=0
->
1 * s_0  +  1 * s_1 * tx  +  1 * s_2 * x  +  1 * s_3 * y >= 0

"""

if __name__ == '__main__':

    # p = multiprocessing.Process(target=run_on_file, args=[sys.argv[1], sys.argv[2]])
    # p.start()
    # p.join(20)
    # if p.is_alive():
    #     print("time limit")
    #     p.kill()
    #     p.join()
    #     with open("./result_" + sys.argv[2]+ "_" + sys.argv[1], "w") as fp:
    #         fp.write( "time limit\n" )

    fileName = './inputs/'
    onlyfiles = [f for f in listdir(fileName) if isfile(join(fileName, f))]
    data = {
        'name': [],
        'bclt': [],
        'z3': [],
        'mathsat': []
    }
    for file in sorted(onlyfiles):
        data['name'].append(file)
        for solver_name in ['bclt', 'z3', 'mathsat']:
            try:
                with open(f'./output/result_{solver_name}_' + file, 'r') as fp:
                    lines = fp.read().split('\n')
                    if lines[0].startswith('time') or lines[1] == 'False':
                        data[solver_name].append(0)
                    else:
                        data[solver_name].append(round(float(lines[0])))
            except:
                data[solver_name].append(0)

    df = pd.DataFrame(data=data)
    df.to_excel('dict1.xlsx')
    ehsan = pd.read_excel('ehsan.xlsx')
    print(int(ehsan[ehsan['name'] == '2Nested_false-termination.c.t2_mult.t2']['bclt']))
    diff = {
        'names': [],
        'bclt': [],
        'z3': [],
        'mathsat': []
    }
    for name in ehsan['name']:
        diff['names'].append(name)
        for solver_name in ['bclt', 'z3', 'mathsat']:

            if int(ehsan[ehsan['name'] == name][solver_name]) == 0 and int(df[df['name'] == name][solver_name]) != 0:
                diff[solver_name].append(1)
                print(1, name, solver_name)
            elif int(ehsan[ehsan['name'] == name][solver_name]) != 0 and int(df[df['name'] == name][solver_name]) == 0:
                diff[solver_name].append(2)
                print(2, name, solver_name)

            else:
                diff[solver_name].append(0)

    diff = pd.DataFrame(data=diff)
    for solver_name in ['bclt', 'z3', 'mathsat']:
        print(solver_name)
        print(diff[solver_name].value_counts())
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
    # output_farkas = subprocess.getoutput("./solver/z3 checking.txt")
    # print('salam ' + output_farkas)
    # Solver.core_iteration(all_constraint)
    # convert_string_to_set_of_variables('declare program vars x y')
    # print(convert_general_string_to_poly('x+--+y' , SetOfVariables.all_declared_var, SetOfVariables.program_declared_var))

    # c1 = CoefficientConstraint(model.get_polynomial('c_1-2').monomials[0].coefficient, '<')
    # c2 = CoefficientConstraint(model.get_polynomial('c_2+1').monomials[0].coefficient, '>=')
    # c3 = CoefficientConstraint(model.get_polynomial('c_3-c_1').monomials[0].coefficient, '>=')
    # c4 = CoefficientConstraint(model.get_polynomial('s_0-1').monomials[0].coefficient, '>=')
    #
    # dnf = DNF([[c1], [c3, c4]])
    # dnf2 = DNF([[c3, c2], [c2,c4]])
    # print(dnf.convert_to_preorder())
    # print(-dnf)
    # model.add_paired_constraint(dnf, dnf2)
    # print(model)
