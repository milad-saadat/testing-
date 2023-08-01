class UnknownVariable:
    new_id = 0
    dict_from_name_to_variable = {}
    all_variables = []

    @staticmethod
    def get_new_id():
        UnknownVariable.new_id += 1
        return UnknownVariable.new_id

    @staticmethod
    def get_variable_by_name(name):
        if name in UnknownVariable.dict_from_name_to_variable.keys():
            return UnknownVariable.dict_from_name_to_variable[name]
        else:
            print(f'there is not such variable with name : {name}')
            return None
    @staticmethod
    def get_variable_by_id(id_to_find):
        return UnknownVariable.all_variables[id_to_find - 1]

    def __init__(self, name=None, typ=None):
        self.name = name
        self.type = typ
        self.id = UnknownVariable.get_new_id()
        UnknownVariable.dict_from_name_to_variable[name] = self
        UnknownVariable.all_variables.append(self)

    def __str__(self):
        if self.name is not None:
            return self.name+ f'_{self.id}'
        return str(f'var_{self.id}[{self.name}]')

    def __lt__(self, other):
        return self.id < other.id

    def __eq__(self, other):
        return self.id == other.id

    def convert_to_preorder(self):
        return f'(/ {self.name}_num {self.name}_den)'
