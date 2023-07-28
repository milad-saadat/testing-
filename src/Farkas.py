from src.Constraint import PolynomialConstraint
from src.Solver import Solver
from src.Polynomial import Polynomial
from src.Constraint import CoefficientConstraint


class Farkas:
    def __init__(self, variables, LHS: [PolynomialConstraint], RHS: PolynomialConstraint):
        self.variables = variables
        self.RHS = RHS
        self.LHS = LHS

    def get_poly_sum(self, need_strict=False):
        new_var = Solver.get_variable_polynomial(self.variables, 'lambda0', 'generated_for_Farkas')
        polynomial_of_sum = new_var

        sum_of_strict = Polynomial(self.variables, [])

        constraints = [CoefficientConstraint(new_var.monomials[0].coefficient, '>=')]

        for i, left_constraint in enumerate(self.LHS):
            left_poly = left_constraint.polynomial
            new_var_poly = Solver.get_variable_polynomial(self.variables, f'lambda{i + 1}',
                                                          'generated_for_Farkas')
            if left_constraint.is_strict():
                sum_of_strict = sum_of_strict + new_var_poly

            polynomial_of_sum = polynomial_of_sum + (new_var_poly * left_poly)
            constraints.append(CoefficientConstraint(new_var_poly.monomials[0].coefficient, '>='))

        if need_strict:
            constraints.append(CoefficientConstraint(sum_of_strict.monomials[0].coefficient, '>'))
        return polynomial_of_sum, constraints

    def get_SAT_constraint(self):
        polynomial_of_sum, constraints = self.get_poly_sum()
        return Solver.find_equality_constrain(polynomial_of_sum, self.RHS.polynomial) + constraints

    def get_UNSAT_constraint(self, need_strict=False):
        if need_strict:
            polynomial_of_sum, constraints = self.get_poly_sum(need_strict)
            return Solver.find_equality_constrain(polynomial_of_sum,
                                                  Polynomial(polynomial_of_sum.variables, [])) + constraints
        polynomial_of_sum, constraints = self.get_poly_sum()
        return Solver.find_equality_constrain(polynomial_of_sum,
                                              Solver.get_constant_polynomial(self.RHS.polynomial.variables, '-1')) + \
            constraints
