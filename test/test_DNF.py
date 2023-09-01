import unittest

from src.Constraint import CoefficientConstraint
from src.DNF import DNF
from src.PositiveModel import *


class MyTestCase(unittest.TestCase):
    def test_dnf_or(self):
        model = PositiveModel(['c_1', 'c_2', 'c_3', 's_0'], [], model_name=Theorem.Farkas)
        c1 = CoefficientConstraint(model.get_polynomial('c_1-2').monomials[0].coefficient, '<')
        c2 = CoefficientConstraint(model.get_polynomial('c_2+1').monomials[0].coefficient, '>=')
        c3 = CoefficientConstraint(model.get_polynomial('c_3-c_1').monomials[0].coefficient, '>=')
        c4 = CoefficientConstraint(model.get_polynomial('s_0-1').monomials[0].coefficient, '>=')

        dnf1 = DNF([[c1], [c3, c4]])
        dnf2 = DNF([[c3, c2], [c2, c4]])
        dnf_res = DNF([[c1], [c3, c4], [c3, c2], [c2, c4]])
        self.assertEqual(str(dnf_res), str(dnf1 | dnf2))  # add assertion here

    def test_dnf_and(self):
        model = PositiveModel(['c_1', 'c_2', 'c_3', 's_0'], [], model_name=Theorem.Farkas)
        c1 = CoefficientConstraint(model.get_polynomial('c_1-2').monomials[0].coefficient, '<')
        c2 = CoefficientConstraint(model.get_polynomial('c_2+1').monomials[0].coefficient, '>=')
        c3 = CoefficientConstraint(model.get_polynomial('c_3-c_1').monomials[0].coefficient, '>=')
        c4 = CoefficientConstraint(model.get_polynomial('s_0-1').monomials[0].coefficient, '>=')

        dnf1 = DNF([[c1], [c3, c4]])
        dnf2 = DNF([[c3, c2], [c2, c4]])
        dnf_res = DNF([[c1, c3, c2], [c1, c2, c4], [c3, c4, c3, c2], [c3, c4, c2, c4]])
        self.assertEqual(dnf_res.convert_to_preorder(), (dnf1 & dnf2).convert_to_preorder())

    def test_dnf_neg(self):
        model = PositiveModel(['c_1', 'c_2', 'c_3', 's_0'], [], model_name=Theorem.Farkas)
        c1 = CoefficientConstraint(model.get_polynomial('c_1-2').monomials[0].coefficient, '<')
        c2 = CoefficientConstraint(model.get_polynomial('c_2+1').monomials[0].coefficient, '>=')
        c3 = CoefficientConstraint(model.get_polynomial('c_3-c_1').monomials[0].coefficient, '>=')
        c4 = CoefficientConstraint(model.get_polynomial('s_0-1').monomials[0].coefficient, '>=')

        dnf1 = DNF([[c1], [c3, c4]])
        dnf_res = DNF([[-c1, -c3], [-c1, -c4]])
        self.assertEqual(str(-dnf1), str(dnf_res))


if __name__ == '__main__':
    unittest.main()
