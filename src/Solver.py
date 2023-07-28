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
                smt_string = smt_string + f'(assert  {constraint.convert_to_preorder()} )\n'
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




