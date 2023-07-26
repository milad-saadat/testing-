# from src.Element import Element
import numpy as np
from src.UnknownVariable import UnknownVariable
from fractions import Fraction


class Element:

    def __init__(self, constant, variables: [UnknownVariable] = []):
        self.constant = Fraction(constant)
        variables.sort()
        self.variables = variables

    def __str__(self):
        return '*'.join([str(self.constant)] + [str(var) for var in self.variables])

    def __mul__(self, other):
        return Element((self.constant * other.constant), (self.variables + other.variables))

    def __add__(self, other):
        return Coefficient([self, other])

    def __lt__(self, other):
        if len(self.variables) == len(other.variables):
            for i in range(len(self.variables)):
                if not (self.variables[i] == other.variables[i]):
                    return self.variables[i] < other.variables[i]
            return True
        else:
            return len(self.variables) < len(other.variables)

    def __eq__(self, other):
        if len(self.variables) == len(other.variables):
            for i in range(len(self.variables)):
                if not (self.variables[i] == other.variables[i]):
                    return False
            return True
        else:
            return False

    def __neg__(self):
        return Element(-self.constant, self.variables)

    def convert_to_preorder(self):

        preorder = f'(/ {self.constant.numerator} {self.constant.denominator})'
        if self.constant < 0:
            preorder = f'(- (/ {-self.constant.numerator} {self.constant.denominator}))'

        for var in self.variables:
            preorder = '( * ' + preorder + ' ' + str(var) + ')'
        return preorder


class Coefficient:

    def __init__(self, elements: [Element] = []):
        elements.sort()
        self.elements = elements

    def __str__(self):
        if len(self.elements) == 0:
            return '0'
        return '+'.join([str(element) for element in self.elements])

    def __mul__(self, other):
        return Coefficient(
            np.array(
                np.matmul(
                    np.array(self.elements).reshape(1, -1).T,
                    np.array(other.elements).reshape(1, -1)
                )
            ).reshape(1, -1)[0]
        ).revise()

    def __add__(self, other):
        if type(other) is Coefficient:
            return Coefficient(self.elements + other.elements).revise()
        if type(other) is Element:
            return Coefficient(self.elements + [other]).revise()

    def revise(self):
        self.elements.sort()
        new_list = []
        i = 0
        while i < len(self.elements):
            constant = Fraction('0')
            j = i
            while j < len(self.elements):
                if self.elements[i] == self.elements[j]:
                    constant += self.elements[j].constant
                else:
                    break
                j += 1
            new_list.append(Element(constant, self.elements[i].variables))
            i = j

        return Coefficient(new_list)

    def __neg__(self):
        elements = [-element for element in self.elements]
        return Coefficient(elements)

    def __sub__(self, other):
        return self + (-other)

    def convert_to_preorder(self):
        if len(self.elements) == 0:
            return '0'
        preorder = self.elements[0].convert_to_preorder()
        for i in range(1, len(self.elements)):
            preorder = '( + ' + preorder + ' ' + self.elements[i].convert_to_preorder() + ')'
        return preorder
