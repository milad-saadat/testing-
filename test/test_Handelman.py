import unittest

from src.PositiveModel import *


class MyTestCase(unittest.TestCase):
    def test_lst_with_fixed_len(self):
        UnknownVariable.number_of_variables = 0
        model = PositiveModel([], ['x'], None)
        poly1 = model.get_polynomial(
            '1 + (-1)*x')
        poly2 = model.get_polynomial(
            '1 + (1)*x')
        poly4 = model.get_polynomial(
            '(1)*x^2')

        constraint1 = PolynomialConstraint(poly1, '>=')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint4 = PolynomialConstraint(poly4, '>')
        handelman = Handelman(poly1.variables, [constraint1, constraint2], constraint4, max_d_for_sat=2)
        for lst in handelman.get_lists_with_fixed_len([], 5, 4):
            print(lst)

    def test_SAT_Handelman(self):
        # example of second article
        UnknownVariable.number_of_variables = 0
        model = PositiveModel([], ['x'], None)
        poly1 = model.get_polynomial(
            '1 + (-1)*x')
        poly2 = model.get_polynomial(
            '1 + (1)*x')
        poly4 = model.get_polynomial(
            '(1)*x^2')

        constraint1 = PolynomialConstraint(poly1, '>=')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint4 = PolynomialConstraint(poly4, '>')
        handelman = Handelman(poly1.variables, [constraint1, constraint2], constraint4, max_d_for_sat=2)

        all_constraint = handelman.get_SAT_constraint()
        answer_string = ''
        for con in all_constraint:
            answer_string += str(con)
            answer_string += '\n'

        actual_answer = '1*y0_2+1*y1_3+1*y2_4+1*y3_5+1*y4_6+1*y5_7+1*y6_8=0\n' + \
                        '-1*y2_4+-2*y3_5+1*y4_6+0*y5_7+2*y6_8=0\n' + \
                        '-1+1*y3_5+-1*y5_7+1*y6_8=0\n' + \
                        '1*y0_2>0\n' + \
                        '1*y1_3>=0\n' + \
                        '1*y2_4>=0\n' + \
                        '1*y3_5>=0\n' + \
                        '1*y4_6>=0\n' + \
                        '1*y5_7>=0\n' + \
                        '1*y6_8>=0\n' + \
                        '0+1*y1_3>0\n'
        self.assertEqual(actual_answer, answer_string)


if __name__ == '__main__':
    unittest.main()
