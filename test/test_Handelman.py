import unittest

from src.Constraint import *
from src.Handelman import Handelman
from src.Parser import *
from src.Solver import *

class MyTestCase(unittest.TestCase):
    def test_SAT_Handelman(self):
        # example of second article
        convert_string_to_set_of_variables('declare program vars x ')
        poly1 = convert_string_to_polynomial(
            '(1)*x^0 + (-1)*x^1')
        poly2 = convert_string_to_polynomial(
            '(1)*x^0 + (1)*x^1')
        poly4 = convert_string_to_polynomial(
            '(1)*x^2')

        constraint1 = PolynomialConstraint(poly1, '>=')
        constraint2 = PolynomialConstraint(poly2, '>=')
        constraint4 = PolynomialConstraint(poly4, '>')
        handelman = Handelman(poly1.variables, [constraint1, constraint2], constraint4)

        all_constraint = handelman.get_SAT_constraint(2)
        answer_string = ''
        for con in all_constraint:
            answer_string += str(con)
            answer_string += '\n'
        actual_answer = '1*lambda1+1*lambda2+1*lambda3+1*lambda4+1*lambda5+1*lambda6=0\n' + \
                        '-1*lambda2+-2*lambda3+1*lambda4+0*lambda5+2*lambda6=0\n' + \
                        '-1+1*lambda3+-1*lambda5+1*lambda6=0\n' + \
                        '1*lambda1>=0\n' +\
                        '1*lambda2>=0\n' +\
                        '1*lambda3>=0\n' +\
                        '1*lambda4>=0\n' +\
                        '1*lambda5>=0\n' +\
                        '1*lambda6>=0\n'

        self.assertEqual(actual_answer, answer_string)


if __name__ == '__main__':
    unittest.main()
# '1*y0+1*lambda1+1*lambda2+1*lambda3+1*lambda4+1*lambda5+1*lambda6=0\n'
#  '-1*lambda2+-2*lambda3+1*lambda4+0*lambda5+2*lambda6=0\n'
#  '-1+1*lambda3+-1*lambda5+1*lambda6=0\n'
#  '1*y0>0\n'
#
# '1*lambda1+1*lambda2+1*lambda3+1*lambda4+1*lambda5+1*lambda6=0\n'
#  '-1*lambda2+-2*lambda3+1*lambda4+0*lambda5+2*lambda6=0\n'
#  '-1+1*lambda3+-1*lambda5+1*lambda6=0\n'
