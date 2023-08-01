from src.Polynomial import Polynomial
from src.Coefficient import Coefficient


class PolynomialConstraint:
    def __init__(self, polynomial: Polynomial, sign: str):
        self.polynomial = polynomial
        self.sign = sign
        if sign == '<':
            self.sign = '>'
            self.polynomial = -self.polynomial
        if sign == '<=':
            self.sign = '>='
            self.polynomial = -self.polynomial

    def __str__(self):
        return str(self.polynomial) + self.sign + "0"

    def is_strict(self):
        return self.sign == '>'

    def __neg__(self):
        if self.sign == '>':
            return PolynomialConstraint(-self.polynomial, '>=')
        elif self.sign == '>=':
            return PolynomialConstraint(-self.polynomial, '>')
        elif self.sign == '=':
            return PolynomialConstraint(self.polynomial, '!=')
        elif self.sign == '!=':
            return PolynomialConstraint(self.polynomial, '=')

class CoefficientConstraint:
    def __init__(self, coefficient: Coefficient, sign: str):
        self.coefficient = coefficient
        self.sign = sign

    def __str__(self):
        return str(self.coefficient) + self.sign + "0"

    def is_strict(self):
        return self.sign == '>'

    def convert_to_preorder(self):
        return '(' + self.sign + ' ' + self.coefficient.convert_to_preorder() + ' ' + '0)'

    def is_equality(self):
        if self.sign != '=' or len(self.coefficient.elements) > 2:
            return False
        if len(self.coefficient.elements) == 2:
            if len(self.coefficient.elements[0].variables) + len(self.coefficient.elements[1].variables) == 1:
                return True
            else:
                return False
        if len(self.coefficient.elements) == 1:
            if len(self.coefficient.elements[0].variables)  == 1:
                return True
            else:
                return False
