from src.Constraint import PolynomialConstraint
from src.Solver import Solver
from src.Polynomial import Polynomial
from src.Constraint import CoefficientConstraint


class Handelman:
    def __init__(self, variables, LHS: [PolynomialConstraint], RHS: PolynomialConstraint):
        self.variables = variables
        self.RHS = RHS
        self.LHS = LHS

    def get_monoids(self, max_d):
        monoids = []
        for mask in range((max_d + 1) ** (len(self.LHS))):
            mask_copy = mask
            degree_of_each_lhs = []
            for i in range(len(self.LHS)):
                degree_of_each_lhs.append(mask_copy % (max_d + 1))
                mask_copy //= (max_d + 1)

            if sum(degree_of_each_lhs) > max_d:
                continue
            poly = Solver.get_constant_polynomial(self.variables, '1')
            for i in range(len(self.LHS)):
                for d in range(degree_of_each_lhs[i]):
                    poly = poly * self.LHS[i].polynomial
            monoids.append(poly)
        return monoids

    def get_poly_sum(self, max_d):
        polynomial_of_sum = Polynomial(self.variables, [])

        all_monoid = self.get_monoids(max_d)
        constraints = []

        if self.RHS.is_strict():
            new_var = Solver.get_variable_polynomial(self.variables, 'y0', 'generated_for_handelman_in_strict_case')
            polynomial_of_sum = polynomial_of_sum + new_var
            constraints.append(CoefficientConstraint(new_var.monomials[0].coefficient, '>'))

        for i, monoid in enumerate(all_monoid):
            new_var_poly = Solver.get_variable_polynomial(self.variables, f'lambda{i + 1}',
                                                          'generated_for_Handelman')
            polynomial_of_sum = polynomial_of_sum + (new_var_poly * monoid)
            constraints.append(CoefficientConstraint(new_var_poly.monomials[0].coefficient, '>='))
        return polynomial_of_sum, constraints

    def get_SAT_constraint(self, max_d):
        polynomial_of_sum, constraints = self.get_poly_sum(max_d)
        return Solver.find_equality_constrain(polynomial_of_sum, self.RHS.polynomial) + constraints

    def get_UNSAT_constraint(self, max_d):
        polynomial_of_sum, constraints = self.get_poly_sum(max_d)
        return Solver.find_equality_constrain(polynomial_of_sum,
                                              Solver.get_constant_polynomial(self.RHS.polynomial.variables, '-1')) + constraints
