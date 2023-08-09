import unittest
from src.Parser import *
from src.Constraint import *
from src.Solver import *
from src.Putinar import Putinar


class MyTestCase(unittest.TestCase):
    def test_get_semidefinite_mat(self):
        UnknownVariable.number_of_variables = 0
        convert_string_to_set_of_variables('declare vars x')

        poly1 = convert_string_to_polynomial(
            '(1)*x^0 + (-1)*x^1')
        poly2 = convert_string_to_polynomial(
            '(1)*x^0 + (1)*x^1')
        poly4 = convert_string_to_polynomial(
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

        actual = '(1*l_00*l_00)*x^0    (1*l_00*l_10)*x^0    (1*l_00*l_20)*x^0    \n' + \
                 '(1*l_00*l_10)*x^0    (1*l_10*l_10+1*l_11*l_11)*x^0    (1*l_10*l_20+1*l_11*l_21)*x^0    \n' + \
                 '(1*l_00*l_20)*x^0    (1*l_10*l_20+1*l_11*l_21)*x^0    (1*l_20*l_20+1*l_21*l_21+1*l_22*l_22)*x^0    \n'

        self.assertEqual(ans, actual)

    def test_get_monoid(self):
        x = UnknownVariable('x')
        y = UnknownVariable('y')

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
        x = UnknownVariable('x')
        y = UnknownVariable('y')

        putinar = Putinar([x, y], [], None)
        ans = str(putinar.get_sum_of_square(2)[0])

        actual = '(1*l_00*l_00)*x^0*y^0+(2*l_00*l_20)*x^0*y^1+(1*l_20*l_20+1*l_21*l_21+1*l_22*l_22)*x^0*y^2+(' \
                 '2*l_00*l_10)*x^1*y^0+(2*l_10*l_20+2*l_11*l_21)*x^1*y^1+(1*l_10*l_10+1*l_11*l_11)*x^2*y^0'

        self.assertEqual(ans, actual)  # add assertion here

    def test_get_template(self):
        UnknownVariable.number_of_variables = 0
        convert_string_to_set_of_variables('declare template vars c1 c2 c3 c4')
        convert_string_to_set_of_variables('declare program vars x y')

        poly1 = convert_string_to_polynomial(
            '(1*c1)*x^1*y^0')
        poly2 = convert_string_to_polynomial(
            '(1*c2)*x^0*y^1')
        poly3 = convert_string_to_polynomial(
            '(1*c3)*x^1*y^1 + (1*c4)*x^0*y^0')

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

        self.assertEqual(ans, actual)  # add assertion here

    def test_get_UNSAT_constraint_for_strict(self):
        UnknownVariable.number_of_variables = 0
        convert_string_to_set_of_variables('declare template vars c1 c2 c3 c4')
        convert_string_to_set_of_variables('declare program vars x y')

        poly1 = convert_string_to_polynomial(
            '(1*c1)*x^1*y^0')
        poly2 = convert_string_to_polynomial(
            '(1*c2)*x^0*y^1')
        poly3 = convert_string_to_polynomial(
            '(1*c3)*x^1*y^1 + (1*c4)*x^0*y^0')

        constraint1 = PolynomialConstraint(poly1, '>')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint3 = PolynomialConstraint(poly3, '>')

        putinar = Putinar(constraint1.polynomial.variables, [constraint1, constraint2], constraint3)

        all_con = putinar.get_UNSAT_constraint(1, True, 1)
        ans = ''
        for con in all_con[0]:
            ans += str(con) + '\n'

        actual = '1*eta5=0\n' + \
                 '1*eta2=0\n' + \
                 '1*eta4=0\n' + \
                 '-1*c2*eta1=0\n' + \
                 '-1*c2*eta4=0\n' + \
                 '-1*c1*eta2=0\n' + \
                 '1*eta3=0\n' + \
                 '-1*c2*eta3=0\n' + \
                 '1*eta1=0\n' + \
                 '-1*c1*eta1=0\n' + \
                 '-1*c2*eta5=0\n' + \
                 '-1*c1*eta3+-1*c2*eta2=0\n' + \
                 '1*eta5=0\n' + \
                 '1*eta4=0\n' + \
                 '-1*c1*eta4=0\n' + \
                 '1*eta2=0\n' + \
                 '1+1*eta1=0\n' + \
                 '-1*c1*eta5=0\n' + \
                 '1*eta3=0\n'

        self.assertEqual(ans, actual)  # add assertion here

    def test_get_SAT_constraint_for_strict(self):
        UnknownVariable.number_of_variables = 0
        convert_string_to_set_of_variables('declare vars c1 c2 c3 c4')
        convert_string_to_set_of_variables('declare vars x y')

        poly1 = convert_string_to_polynomial(
            '(1*c1)*x^1*y^0')
        poly2 = convert_string_to_polynomial(
            '(1*c2)*x^0*y^1')
        poly3 = convert_string_to_polynomial(
            '(1*c3)*x^1*y^1 + (1*c4)*x^0*y^0')

        constraint1 = PolynomialConstraint(poly1, '>')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint3 = PolynomialConstraint(poly3, '>')

        putinar = Putinar(constraint1.polynomial.variables, [constraint1, constraint2], constraint3)

        all_con = putinar.get_SAT_constraint(1)
        ans = ''
        for con in all_con:
            ans += str(con) + '\n'

        actual = '1*l_00>=0\n' + \
                 '1*l_11>=0\n' + \
                 '1*l_22>=0\n' + \
                 '1*l_00>=0\n' + \
                 '1*l_11>=0\n' + \
                 '1*l_22>=0\n' + \
                 '1*l_00>=0\n' + \
                 '1*l_11>=0\n' + \
                 '1*l_22>=0\n' + \
                 '2*l_00*l_20+1*c2*l_00*l_00=0\n' + \
                 '2*c2*l_00*l_20=0\n' + \
                 '-1*c4+1*l_00*l_00=0\n' + \
                 '2*l_00*l_10+1*c1*l_00*l_00=0\n' + \
                 '-1*c3+2*c1*l_00*l_20+2*c2*l_00*l_10=0\n' + \
                 '2*c1*l_00*l_10=0\n'

        self.assertEqual(ans, actual)  # add assertion here


if __name__ == '__main__':
    unittest.main()
