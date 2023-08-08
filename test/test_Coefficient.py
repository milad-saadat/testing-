import unittest
from src.Coefficient import Element
from src.UnknownVariable import UnknownVariable
from src.Coefficient import Coefficient


class MyTestCase(unittest.TestCase):
    def test_converting_to_string1(self):
        UnknownVariable.number_of_variables = 0

        a = UnknownVariable('a')
        element1 = Element('7/10', [a, a])
        self.assertEqual('7/10*a*a', str(element1))

    def test_converting_to_string2(self):
        UnknownVariable.number_of_variables = 0

        a = UnknownVariable('a')
        b = UnknownVariable('b')
        element2 = Element('1.3', [a, b])
        self.assertEqual('13/10*a*b', str(element2))

    def test_multiply_Element(self):
        UnknownVariable.number_of_variables = 0
        a = UnknownVariable('a')
        element1 = Element('7/10', [a, a])
        b = UnknownVariable('b')
        element2 = Element('1.3', [a, b])
        self.assertEqual('91/100*a*a*a*b', str(element1 * element2))

    def test_multiply_Coefficient(self):
        # (7/10 a + 1.3 a b) * (2 + 3b) = 7/5 a + 47/10 a b + 39/10 a b b
        UnknownVariable.number_of_variables = 0
        a = UnknownVariable('a')
        b = UnknownVariable('b')

        element1 = Element(constant='7/10', variables=[a])
        element2 = Element('1.3', [a, b])
        element3 = Element('2', [])
        element4 = Element('3', [b])

        coef1 = Coefficient([element1, element2])
        coef2 = Coefficient([element3, element4])

        self.assertEqual('7/5*a+47/10*a*b+39/10*a*b*b', str(coef1 * coef2))

    def test_add_Coefficient(self):
        # (7/10 a + 1.3 a b) + (2 a + 3b) = 27/10 a + 3b + 1.3 ab
        UnknownVariable.number_of_variables = 0
        a = UnknownVariable('a')
        b = UnknownVariable('b')

        element1 = Element(constant='7/10', variables=[a])
        element2 = Element('1.3', [a, b])
        element3 = Element('2', [a])
        element4 = Element('3', [b])

        coef1 = Coefficient([element1, element2])
        coef2 = Coefficient([element3, element4])

        self.assertEqual('27/10*a+3*b+13/10*a*b', str(coef1 + coef2))

    def test_add_Coefficient_with_Element(self):
        # (7/10 a + 1.3 a b) + (2 a) = 27/10 a + 1.3 ab
        UnknownVariable.number_of_variables = 0
        a = UnknownVariable('a')
        b = UnknownVariable('b')

        element1 = Element(constant='7/10', variables=[a])
        element2 = Element('1.3', [a, b])
        element3 = Element('2', [a])

        coef1 = Coefficient([element1, element2])

        self.assertEqual('27/10*a+13/10*a*b', str(coef1 + element3))

    def test_convert_to_string_zero(self):
        coef1 = Coefficient([])
        self.assertEqual('0', str(coef1))

    def test_add_Element(self):
        # (7/10 a + 1.3 a b) + (2 a + 3b) = 27/10 a + 3b + 1.3 ab
        UnknownVariable.number_of_variables = 0
        a = UnknownVariable('a')
        b = UnknownVariable('b')

        element1 = Element(constant='7/10', variables=[a])
        element2 = Element('1.3', [a, b])

        coef1 = Coefficient([element1, element2])

        self.assertEqual(str(coef1), str(element1 + element2))

    def test_compare_Element(self):
        # (7/10 a + 1.3 a b) + (2 a + 3b) = 27/10 a + 3b + 1.3 ab
        UnknownVariable.number_of_variables = 0
        a = UnknownVariable('a')
        b = UnknownVariable('b')

        element1 = Element(constant='7/10', variables=[a])
        element2 = Element('1.3', [b])

        self.assertEqual(False, element1 == element2)
        self.assertEqual(True, element1 < element2)


if __name__ == '__main__':
    unittest.main()
