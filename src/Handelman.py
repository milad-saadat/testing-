from src.Constraint import PolynomialConstraint
from src.Solver import Solver
from src.Polynomial import Polynomial
from src.Constraint import CoefficientConstraint


class Handelman:
    def __init__(self, variables, LHS: [PolynomialConstraint], RHS: PolynomialConstraint,
                 max_d_for_sat=0, max_d_for_unsat=0):
        self.variables = variables
        self.RHS = RHS
        self.LHS = LHS
        self.max_d_for_sat = max_d_for_sat
        self.max_d_for_unsat = max_d_for_unsat

    def get_monoids(self, max_d):
        monoids = []
        is_strict = []
        for mask in range((max_d + 1) ** (len(self.LHS))):
            mask_copy = mask
            degree_of_each_lhs = []
            for i in range(len(self.LHS)):
                degree_of_each_lhs.append(mask_copy % (max_d + 1))
                mask_copy //= (max_d + 1)

            if sum(degree_of_each_lhs) > max_d:
                continue
            poly = Solver.get_constant_polynomial(self.variables, '1')
            is_the_new_monoid_strict = True

            for i in range(len(self.LHS)):
                if (not self.LHS[i].is_strict()) and (degree_of_each_lhs[i] > 0):
                    is_the_new_monoid_strict = False
                for d in range(degree_of_each_lhs[i]):
                    poly = poly * self.LHS[i].polynomial

            is_strict.append(is_the_new_monoid_strict)
            monoids.append(poly)
        return monoids, is_strict

    def get_poly_sum(self, max_d, need_strict=False):
        polynomial_of_sum = Polynomial(self.variables, [])

        all_monoid, is_strict = self.get_monoids(max_d)
        constraints = []
        sum_of_strict = Polynomial(self.variables, [])

        if self.RHS.is_strict():
            new_var = Solver.get_variable_polynomial(self.variables, 'y0', 'generated_for_handelman_in_strict_case')
            polynomial_of_sum = polynomial_of_sum + new_var
            constraints.append(CoefficientConstraint(new_var.monomials[0].coefficient, '>'))

        for i, monoid in enumerate(all_monoid):
            new_var_poly = Solver.get_variable_polynomial(self.variables, f'lambda{i + 1}',
                                                          'generated_for_Handelman')
            polynomial_of_sum = polynomial_of_sum + (new_var_poly * monoid)
            constraints.append(CoefficientConstraint(new_var_poly.monomials[0].coefficient, '>='))

            if is_strict[i]:
                sum_of_strict = sum_of_strict + new_var_poly

        if need_strict:
            constraints.append(CoefficientConstraint(sum_of_strict.monomials[0].coefficient, '>'))

        return polynomial_of_sum, constraints

    def get_SAT_constraint(self):
        polynomial_of_sum, constraints = self.get_poly_sum(self.max_d_for_sat)
        return Solver.find_equality_constrain(polynomial_of_sum, self.RHS.polynomial) + constraints

    def get_UNSAT_constraint(self, need_strict=False):
        if need_strict:
            polynomial_of_sum, constraints = self.get_poly_sum(need_strict)
            return Solver.find_equality_constrain(polynomial_of_sum,
                                                  Polynomial(polynomial_of_sum.variables, [])) + constraints

        polynomial_of_sum, constraints = self.get_poly_sum(self.max_d_for_unsat)
        return Solver.find_equality_constrain(polynomial_of_sum,
                                              Solver.get_constant_polynomial(self.variables, '-1')) + constraints
