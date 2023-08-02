class UnknownVariable:
    new_id = 0

    @staticmethod
    def get_new_id():
        UnknownVariable.new_id += 1
        return UnknownVariable.new_id

    def __init__(self, name=None, typ=None):
        self.name = name
        self.type = typ
        self.id = UnknownVariable.get_new_id()

    def __str__(self):
        if self.name is not None:
            return self.name + f'_{self.id}'
        return str(f'var_{self.id}[{self.name}]')

    def __lt__(self, other):
        return self.id < other.id

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return hash(self.id)

    def convert_to_preorder(self):
        return f'(/ {self.name}_num {self.name}_den)'
