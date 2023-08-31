import unittest


from src.Farkas import Farkas
from src.PositiveModel import *
from src.Constraint import PolynomialConstraint
class MyTestCase(unittest.TestCase):
    def test_Farkas_SAT(self):
        # First example of first article
        UnknownVariable.number_of_variables=0

        model = PositiveModel(['c1', 'c2', 'd'], ['i', 'j', 'ip', 'jp'], None)
        constraint1 = PolynomialConstraint(model.get_polynomial('(1*c1)*i^1 + (1*c2)*j^1 + (1*d)') ,'>=')
        constraint2 = PolynomialConstraint(model.get_polynomial('(1)*i^1 + (-1)*ip^1 + 4') ,'>=')

        constraint3 = PolynomialConstraint(model.get_polynomial('1*j^1 + (-1)*jp^1') ,'>=')
        constraint4 = PolynomialConstraint(model.get_polynomial('(1*c1)*ip^1 + (1*c2)*jp^1 + d') ,'>=')

        frakas = Farkas(constraint1.polynomial.variables, [constraint1, constraint2, constraint3], constraint4)
        all_constraint = frakas.get_SAT_constraint()
        answer_string = ''
        for con in all_constraint:
            answer_string += str(con)
            answer_string += '\n'

        actual_answer = '-1*c2+-1*y3_11=0\n' + \
                        '-1*c1+-1*y2_10=0\n' + \
                        '1*y3_11+1*c2*y1_9=0\n' + \
                        '1*y2_10+1*c1*y1_9=0\n' + \
                        '-1*d+1*y0_8+4*y2_10+1*d*y1_9=0\n' + \
                        '1*y0_8>=0\n' + \
                        '1*y1_9>=0\n' + \
                        '1*y2_10>=0\n' + \
                        '1*y3_11>=0\n'

        self.assertEqual(actual_answer, answer_string)


if __name__ == '__main__':
    unittest.main()
