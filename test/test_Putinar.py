import unittest

from src.PositiveModel import *
class MyTestCase(unittest.TestCase):
    def test_get_semidefinite_mat(self):
        UnknownVariable.number_of_variables = 0
        model = PositiveModel([], ['x'], None)
        poly1 = model.get_polynomial(
            '(1)*x^0 + (-1)*x^1')
        poly2 = model.get_polynomial(
            '(1)*x^0 + (1)*x^1')
        poly4 = model.get_polynomial(
            '(1)*x^2')

        constraint1 = PolynomialConstraint(poly1, '>=')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint4 = PolynomialConstraint(poly4, '>')
        putinar = Putinar(constraint1.polynomial.variables, [constraint1, constraint2], constraint4)
        dim = 3
        mat = putinar.get_lower_triangular_matrix(dim)[0]
        ans = ''
        for i in range(mat.shape[0]):
            for j in range(mat.shape[1]):
                ans += str(mat[i][j]) + '    '
            ans += '\n'

        actual = '(1*l_00_2*l_00_2)*x^0    (1*l_00_2*l_10_3)*x^0    (1*l_00_2*l_20_5)*x^0    \n' + \
                 '(1*l_00_2*l_10_3)*x^0    (1*l_10_3*l_10_3+1*l_11_4*l_11_4)*x^0    (1*l_10_3*l_20_5+1*l_11_4*l_21_6)*x^0    \n' + \
                 '(1*l_00_2*l_20_5)*x^0    (1*l_10_3*l_20_5+1*l_11_4*l_21_6)*x^0    (1*l_20_5*l_20_5+1*l_21_6*l_21_6+1*l_22_7*l_22_7)*x^0    \n'

        self.assertEqual(ans, actual)

    def test_get_monoid(self):
        x = UnknownVariable('x', type_of_var="program_var")
        y = UnknownVariable('y', type_of_var="program_var")

        mat = Putinar.get_monoids([x, y], 2)
        ans = ''
        for i in range(len(mat)):
            ans += str(mat[i])
            ans += '\n'

        actual = '(1)*x^0*y^0\n' + \
                 '(1)*x^1*y^0\n' + \
                 '(1)*x^2*y^0\n' + \
                 '(1)*x^0*y^1\n' + \
                 '(1)*x^1*y^1\n' + \
                 '(1)*x^0*y^2\n'

        self.assertEqual(ans, actual)  # add assertion here

    def test_get_sum_of_square(self):
        UnknownVariable.number_of_variables=0
        x = UnknownVariable('x', type_of_var="program_var")
        y = UnknownVariable('y', type_of_var="program_var")

        putinar = Putinar([x, y], [], None)
        ans = str(putinar.get_sum_of_square(2)[0])

        actual = '(1*l_00_3*l_00_3)*x^0*y^0+(2*l_00_3*l_20_6)*x^0*y^1+(' \
                 '1*l_20_6*l_20_6+1*l_21_7*l_21_7+1*l_22_8*l_22_8)*x^0*y^2+(2*l_00_3*l_10_4)*x^1*y^0+(' \
                 '2*l_10_4*l_20_6+2*l_11_5*l_21_7)*x^1*y^1+(1*l_10_4*l_10_4+1*l_11_5*l_11_5)*x^2*y^0'

        self.assertEqual(ans, actual)  # add assertion here

    def test_get_template(self):
        UnknownVariable.number_of_variables = 0
        model = PositiveModel(['c1', 'c2', 'c3', 'c4'], ['x', 'y'], None)

        poly1 = model.get_polynomial(
            'c1*x')
        poly2 = model.get_polynomial(
            'c2*y')
        poly3 = model.get_polynomial(
            '(c3)*x^1*y^1 + (1*c4)*x^0*y^0')

        constraint1 = PolynomialConstraint(poly1, '>')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint3 = PolynomialConstraint(poly3, '>')

        putinar = Putinar(constraint1.polynomial.variables, [constraint1, constraint2], constraint3)
        new_variables = [UnknownVariable(name=f'w_{i + 1}', type_of_var='generated_for_strict_unsat') for i in
                         range(len(putinar.LHS))]

        for left_constraint in putinar.LHS:
            left_constraint.polynomial = left_constraint.polynomial.add_variables(new_variables)
        all_monoids = Putinar.get_monoids(putinar.variables + new_variables, 1)

        ans = str(Putinar.get_general_template(putinar.variables + new_variables, all_monoids))

        actual = '(1*eta1)*x^0*y^0*w_1^0*w_2^0+(1*eta5)*x^0*y^0*w_1^0*w_2^1+(1*eta4)*x^0*y^0*w_1^1*w_2^0+(' \
                 '1*eta3)*x^0*y^1*w_1^0*w_2^0+(1*eta2)*x^1*y^0*w_1^0*w_2^0'
        actual = '(1*eta1_9)*x^0*y^0*w_1_7^0*w_2_8^0+(1*eta5_13)*x^0*y^0*w_1_7^0*w_2_8^1+(' \
                 '1*eta4_12)*x^0*y^0*w_1_7^1*w_2_8^0+(1*eta3_11)*x^0*y^1*w_1_7^0*w_2_8^0+(' \
                 '1*eta2_10)*x^1*y^0*w_1_7^0*w_2_8^0'
        self.assertEqual(ans, actual)  # add assertion here

    def test_get_UNSAT_constraint_for_strict(self):
        UnknownVariable.number_of_variables = 0
        model = PositiveModel(['c1', 'c2', 'c3', 'c4'], ['x', 'y'], None)

        poly1 = model.get_polynomial(
            'c1*x')
        poly2 = model.get_polynomial(
            'c2*y')
        poly3 = model.get_polynomial(
            '(c3)*x^1*y^1 + (1*c4)')


        constraint1 = PolynomialConstraint(poly1, '>')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint3 = PolynomialConstraint(poly3, '>')

        putinar = Putinar(constraint1.polynomial.variables, [constraint1, constraint2], constraint3, max_d_for_unsat_strict=1, max_d_for_unsat=1, degree_for_new_var=1)

        all_con = putinar.get_UNSAT_constraint(True)
        ans = ''
        for con in all_con[0]:
            ans += str(con) + '\n'


        actual = '1*eta5_13=0\n' + \
                 '1*eta2_15=0\n' + \
                 '1*eta4_12=0\n'+ \
                 '-1*c2*eta1_14=0\n'+ \
                 '-1*c2*eta4_17=0\n'+ \
                 '-1*c1*eta2_10=0\n'+ \
                 '1*eta3_11=0\n'+ \
                 '-1*c2*eta3_16=0\n'+ \
                 '1*eta1_14=0\n'+ \
                 '-1*c1*eta1_9=0\n'+ \
                 '-1*c2*eta5_18=0\n'+ \
                 '-1*c1*eta3_11+-1*c2*eta2_15=0\n'+ \
                 '1*eta5_18=0\n'+ \
                 '1*eta4_17=0\n'+ \
                 '-1*c1*eta4_12=0\n'+ \
                 '1*eta2_10=0\n'+ \
                 '1+1*eta1_9=0\n'+ \
                 '-1*c1*eta5_13=0\n'+ \
                 '1*eta3_16=0\n'
        self.assertEqual(ans, actual)  # add assertion here

    def test_get_SAT_constraint_for_strict(self):
        UnknownVariable.number_of_variables = 0
        model = PositiveModel(['c1', 'c2', 'c3', 'c4'], ['x', 'y'], None)

        poly1 = model.get_polynomial(
            'c1*x')
        poly2 = model.get_polynomial(
            'c2*y')
        poly3 = model.get_polynomial(
            '(c3)*x^1*y^1 + (1*c4)*x^0*y^0')


        constraint1 = PolynomialConstraint(poly1, '>')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint3 = PolynomialConstraint(poly3, '>')

        putinar = Putinar(constraint1.polynomial.variables, [constraint1, constraint2], constraint3, max_d_for_sat=1)

        all_con = putinar.get_SAT_constraint()
        ans = ''
        for con in all_con:
            ans += str(con) + '\n'


        actual = '1*l_00_7>=0\n' + \
                 '1*l_11_9>=0\n' + \
                 '1*l_22_12>=0\n' + \
                 '1*y0_13>0\n' + \
                 '1*l_00_14>=0\n' + \
                 '1*l_11_16>=0\n'+ \
                 '1*l_22_19>=0\n'+ \
                 '1*l_00_20>=0\n'+ \
                 '1*l_11_22>=0\n'+ \
                 '1*l_22_25>=0\n'+ \
                 '2*l_00_7*l_20_10+1*c2*l_00_20*l_00_20=0\n'+ \
                 '2*c2*l_00_20*l_20_23=0\n'+ \
                 '-1*c4+1*y0_13+1*l_00_7*l_00_7=0\n'+ \
                 '2*l_00_7*l_10_8+1*c1*l_00_14*l_00_14=0\n'+ \
                 '-1*c3+2*c1*l_00_14*l_20_17+2*c2*l_00_20*l_10_21=0\n'+ \
                 '2*c1*l_00_14*l_10_15=0\n'
        self.assertEqual(ans, actual)  # add assertion here


if __name__ == '__main__':
    unittest.main()
