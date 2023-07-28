import unittest

from src.Parser import *


class MyTestCase(unittest.TestCase):
    def test_multiply(self):
        convert_string_to_set_of_variables('declare template vars a b')
        convert_string_to_set_of_variables('declare program vars x y')
        poly1 = (convert_string_to_polynomial('(5.5*a*a)*x^2*y^0 + (2*b)*x^0*y^0'))
        poly2 = convert_string_to_polynomial('(1*b)*x^0*y^2 + (3*a + 1)*x^0*y^0')
        self.assertEqual(
            "(2*b+6*a*b)*x^0*y^0+(2*b*b)*x^0*y^2+(11/2*a*a+33/2*a*a*a)*x^2*y^0+(11/2*a*a*b)*x^2*y^2",
            str(poly1 * poly2))

    def test_add(self):
        convert_string_to_set_of_variables('declare template vars a b')
        convert_string_to_set_of_variables('declare program vars x y')
        poly1 = (convert_string_to_polynomial('(5.5*a*a)*x^2*y^0 + (2*b)*x^0*y^0'))
        poly2 = convert_string_to_polynomial('(1*b)*x^0*y^2 + (3*a + 1)*x^0*y^0')
        self.assertEqual("(1+3*a+2*b)*x^0*y^0+(1*b)*x^0*y^2+(11/2*a*a)*x^2*y^0", str(poly1 + poly2))


if __name__ == '__main__':
    unittest.main()
