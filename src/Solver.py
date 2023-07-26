import os
import subprocess

from src.Polynomial import Polynomial
from src.Polynomial import Monomial
from src.Coefficient import Coefficient
from src.Coefficient import Element
from src.Constraint import CoefficientConstraint
from src.UnknownVariable import UnknownVariable
from src.Parser import *

class Solver:

    @staticmethod
    def find_equality_constrain(LHS: Polynomial, RHS: Polynomial):
        all_degree = set(
            LHS.dict_from_degrees_to_monomials.keys()
        ).union(
            set(RHS.dict_from_degrees_to_monomials.keys())
        )

        all_constraint = []
        for degree in all_degree:
            mono1 = LHS.get_monomial_by_degree(degree)
            mono2 = RHS.get_monomial_by_degree(degree)
            constraint = CoefficientConstraint(mono1.coefficient - mono2.coefficient, '=')
            all_constraint.append(constraint)

        return all_constraint

    @staticmethod
    def get_constant_polynomial(variables, constant):
        return Polynomial(variables,
                          [Monomial(
                              variables, [0] * len(variables),
                              Coefficient(
                                  [Element(constant, [])]
                              )
                          )]
                          )

    @staticmethod
    def get_variable_polynomial(variables, name, typ=None):
        new_variable = UnknownVariable(name=name, typ=typ)
        return Polynomial(variables,
                          [Monomial(
                              variables, [0] * len(variables),
                              Coefficient(
                                  [Element('1', [new_variable])]
                              )
                          )]
                          )

    @staticmethod
    def get_degree_polynomial(variables, degrees):
        return Polynomial(variables,
                          [Monomial(
                              variables, degrees,
                              Coefficient(
                                  [Element('1', [])]
                              )
                          )]
                          )

    @staticmethod
    def convert_constraints_to_smt_format(all_constraint: [CoefficientConstraint], names = None):
        smt_string = ''
        for i,constraint in enumerate(all_constraint):
            if names is None:
                smt_string = smt_string + f'(assert ( ! {constraint.convert_to_preorder()} ))\n'
            else:
                smt_string = smt_string + f'(assert ( ! {constraint.convert_to_preorder()} :named {names[i]}))\n'
        smt_string = smt_string
        return smt_string

    @staticmethod
    def smt_declare_variable_phase(all_constraint):
        all_variables_ids = set()
        for constraint in all_constraint:
            for element in constraint.coefficient.elements:
                all_variables_ids = all_variables_ids.union(set([var.id for var in element.variables]))

        smt_string = ''

        for var_id in all_variables_ids:
            # smt_string = smt_string + f'(declare-const {var}_num Int)\n'
            # smt_string = smt_string + f'(declare-const {var}_den Int)\n'
            smt_string = smt_string + f'(declare-const {UnknownVariable.get_variable_by_id(var_id)} Real)\n'
        return smt_string

    @staticmethod
    def core_iteration(all_constraint, solver_path = './solver/z3', saving_path = 'save_for_core_iteration_heuristic_temp.txt'):
        template_variables = SetOfVariables.template_declared_var[:]
        unsat = True
        all_constraint[-1].sign = '>'
        all_constraint[-2].sign = '>'
        while unsat and len(template_variables) > 0:
            generated_constraint = []
            new_name = []
            for var in template_variables:
                generated_constraint.append(CoefficientConstraint(Coefficient([Element('1', [var])]), '='))
                new_name.append('cons-'+var.name)

            input_of_solver = '(set-option :produce-unsat-cores true)\n'
            input_of_solver += (Solver.smt_declare_variable_phase(all_constraint))
            input_of_solver += (Solver.convert_constraints_to_smt_format(generated_constraint, new_name))
            input_of_solver += (Solver.convert_constraints_to_smt_format(all_constraint))
            input_of_solver += '\n(check-sat)\n(get-unsat-core)\n'
            # print('------------')
            # print(input_of_solver)
            # print('----------')
            f = open(saving_path, "w")
            f.write(input_of_solver)
            f.close()
            print(input_of_solver)
            output = subprocess.getoutput(f"{solver_path} {saving_path}")

            print(output)
            sat, core = output.split('\n')
            os.remove(saving_path)
            if sat == 'sat':
                unsat = False
                continue
            # print(core[1:-1].split(','))
            for name in core[1:-1].split(' '):
                var = UnknownVariable.get_variable_by_name(name.strip()[5:])
                template_variables.remove(var)

    @staticmethod
    def get_equality_constraint(all_constraint: [CoefficientConstraint]) -> CoefficientConstraint:
        for constraint in all_constraint:
            if constraint.is_equality():
                return constraint
        return None

    @staticmethod
    def remove_equality_constraints(all_constraint: [CoefficientConstraint]):
        while True:
            equality_constraint = Solver.get_equality_constraint(all_constraint)
            if equality_constraint is None:
                break
            variable = None
            amount = 0
            if len(equality_constraint.coefficient.elements) == 1:
                variable = equality_constraint.coefficient.elements[0].variables[0]
            else:
                element1 = equality_constraint.coefficient.elements[0]
                element2 = equality_constraint.coefficient.elements[1]
                if len(element1.variables) == 1:
                    variable = element1.variables[0]
                    amount = -element2.constant / element1.constant
                else:
                    variable = element2.variables[0]
                    amount = -element1.constant / element2.constant
            #todo : add the variable and amount for output later
            all_constraint.remove(equality_constraint)
            for constraint in all_constraint:
                for element in constraint.coefficient.elements:
                    if variable in element.variables:
                        element.variables.remove(variable)
                        element.constant = element.constant * amount
        return all_constraint
