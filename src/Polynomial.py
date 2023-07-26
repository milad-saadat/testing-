import numpy as np
from src.Coefficient import Coefficient
from src.UnknownVariable import UnknownVariable


class Monomial:
    def __init__(self, variables: [UnknownVariable], degrees: [int], coefficient: Coefficient):
        variables.sort()
        self.variables = variables
        self.degrees = degrees
        self.coefficient = coefficient

    def __str__(self):
        return '*'.join(['(' + str(self.coefficient) + ')'] +
                        [str(self.variables[i]) + '^' + str(self.degrees[i]) for i in range(len(self.degrees))])

    def __mul__(self, other):
        return Monomial(self.variables, np.array(self.degrees) + np.array(other.degrees),
                        self.coefficient * other.coefficient)

    def __eq__(self, other):
        if len(self.variables) != len(other.variables):
            return False
        for i in range(len(self.variables)):
            if self.variables[i] != other.variables[i] or self.degrees[i] != other.degrees[i]:
                return False
        return True

    def __lt__(self, other):
        if len(self.variables) != len(other.variables):
            return len(self.variables) < len(other.variables)
        for i in range(len(self.variables)):
            if self.degrees[i] != other.degrees[i]:
                return self.degrees[i] < other.degrees[i]
        return True

    def __neg__(self):
        return Monomial(self.variables, self.degrees, -self.coefficient)


class Polynomial:
    def __init__(self, variables: [UnknownVariable], monomials: [Monomial]):
        variables.sort()
        monomials.sort()
        self.variables = variables
        self.monomials = monomials
        self.dict_from_degrees_to_monomials = {}
        for monomial in self.monomials:
            self.dict_from_degrees_to_monomials[tuple(monomial.degrees)] = monomial

    def get_monomial_by_degree(self, degree):
        if degree in self.dict_from_degrees_to_monomials.keys():
            return self.dict_from_degrees_to_monomials[degree]
        return Monomial(self.variables, [0] * len(self.variables), Coefficient([]))

    def __str__(self):
        if len(self.monomials) == 0:
            return '0'
        return '+'.join([str(monomial) for monomial in self.monomials])

    def __add__(self, other):
        return Polynomial(self.variables, self.monomials + other.monomials).revise()

    def __neg__(self):
        monomials = [-monomial for monomial in self.monomials]
        return Polynomial(self.variables, monomials)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return Polynomial(self.variables,
                          np.array(
                              np.matmul(
                                  np.array(self.monomials).reshape(1, -1).T,
                                  np.array(other.monomials).reshape(1, -1)
                              )
                          ).reshape(1, -1)[0]
                          ).revise()

    def revise(self):
        self.monomials.sort()
        new_list = []
        i = 0
        while i < len(self.monomials):
            coefficient = Coefficient([])
            j = i
            while j < len(self.monomials):
                if self.monomials[i] == self.monomials[j]:
                    coefficient += self.monomials[j].coefficient
                else:
                    break
                j += 1
            new_list.append(Monomial(self.monomials[i].variables, self.monomials[i].degrees, coefficient))
            i = j

        return Polynomial(self.variables, new_list)

    def add_variables(self, new_variables):
        monomials = []
        for monomial in self.monomials:
            monomials.append(Monomial(monomial.variables + new_variables,
                                      monomial.degrees + [0] * len(new_variables),
                                      monomial.coefficient)
                             )
        return Polynomial(self.variables + new_variables, monomials)
