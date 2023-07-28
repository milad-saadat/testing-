import unittest

from src.Constraint import *
from src.Farkas import Farkas
from src.Parser import *
from src.Solver import *


class MyTestCase(unittest.TestCase):
    def test_Farkas_SAT(self):
        convert_string_to_set_of_variables('declare template vars c1 c2 d')
        convert_string_to_set_of_variables('declare program vars  i j ip jp ')
        # First example of first article

        constraint1 = convert_string_to_constraint('(1*c1)*i^1 + (1*c2)*j^1 + (1*d) >= 0')
        constraint2 = convert_string_to_constraint('(1)*i^1 + (-1)*ip^1 + (4) >= 0')
        constraint3 = convert_string_to_constraint('(1)*j^1 + (-1)*jp^1 >= 0')
        constraint4 = convert_string_to_constraint('(1*c1)*ip^1 + (1*c2)*jp^1 + (1*d) >= 0')

        frakas = Farkas(constraint1.polynomial.variables, [constraint1, constraint2, constraint3], constraint4)
        all_constraint = frakas.get_SAT_constraint()
        answer_string = ''
        for con in all_constraint:
            answer_string += str(con)
            answer_string += '\n'

        actual_answer = '-1*c2+-1*lambda3=0\n' + \
                        '-1*c1+-1*lambda2=0\n' + \
                        '1*lambda3+1*c2*lambda1=0\n' + \
                        '1*lambda2+1*c1*lambda1=0\n' + \
                        '-1*d+1*lambda0+4*lambda2+1*d*lambda1=0\n' + \
                        '1*lambda0>=0\n' + \
                        '1*lambda1>=0\n' + \
                        '1*lambda2>=0\n' + \
                        '1*lambda3>=0\n'

        self.assertEqual(actual_answer, answer_string)


if __name__ == '__main__':
    unittest.main()
