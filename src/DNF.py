class DNF:
    def __init__(self, literals):
        self.literals = literals

    def __or__(self, other):
        return DNF(self.literals + other.literals)

    def __and__(self, other):
        if len(self.literals) == 0:
            return DNF(other.literals)
        if len(other.literals) == 0:
            return DNF(self.literals)

        literal_list = []
        for first_literal in self.literals:
            for second_literal in other.literals:
                literal_list.append(first_literal + second_literal)
        return DNF(literal_list)

    def __neg__(self):
        result_DNF = DNF([])
        for literal in self.literals:
            new_arr = []
            for item in literal:
                new_arr.append([-item])
            result_DNF = result_DNF & DNF(new_arr)
        return result_DNF

    def __str__(self):
        res = ''
        for literal in self.literals:
            res += ' AND '.join([str(item) for item in literal])
            res += '\n'
        return '(\n' + res + ')\n'
