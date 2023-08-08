import os
import subprocess

from src.Farkas import *
from src.Handelman import *
from src.Putinar import *
from src.Constant import *
from src.Convertor import *
from src.DNF import *
from src.Coefficient import *
from src.gurobi import *

class PositiveModel:

    def __init__(self, template_variables, program_variables,
                 model_name, get_SAT=True, get_UNSAT=False, get_strict=False, max_d_of_SAT=0,
                 max_d_of_UNSAT=0, max_d_of_strict=0, degree_of_generated_var=0
                 ):
        self.paired_constraint = []
        self.template_variables = []
        self.program_variables = []
        for name in template_variables:
            self.template_variables.append(UnknownVariable(name=name, typ='template_var'))
        for name in program_variables:
            self.program_variables.append(UnknownVariable(name=name, typ='program_var'))

        self.model_name = model_name
        self.get_SAT = get_SAT
        self.get_UNSAT = get_UNSAT
        self.get_strict = get_strict
        self.max_d_of_SAT = max_d_of_SAT
        self.max_d_of_UNSAT = max_d_of_UNSAT
        self.max_d_of_strict = max_d_of_strict
        self.degree_of_generated_var = degree_of_generated_var

    def add_paired_constraint(self, lhs: DNF, rhs: DNF):
        if len(rhs.literals) > 1:
            lhs = lhs & (-(DNF(rhs.literals[1:])))
            rhs = DNF([rhs.literals[0]])
        for literal in lhs.literals:
            for item in rhs.literals[0]:
                self.paired_constraint.append((literal, item))

    def __str__(self):
        res = ''
        for pair in self.paired_constraint:
            for lhs_item in pair[0]:
                res += str(lhs_item) + '\n'
            res += '->\n'
            res += str(pair[1]) + '\n'
            res += '----------------------\n'
        return res

    def get_polynomial(self, poly_str):
        return convert_general_string_to_poly(poly_str, self.template_variables + self.program_variables,
                                              self.program_variables)

    def get_constraints(self):
        all_constraint = []
        for pair in self.paired_constraint:
            if self.model_name == 'farkas':
                model = Farkas(self.program_variables, LHS=pair[0], RHS=pair[1])
            elif self.model_name == 'handelman':
                model = Handelman(self.program_variables, LHS=pair[0], RHS=pair[1],
                                  max_d_for_sat=self.max_d_of_SAT, max_d_for_unsat=self.max_d_of_UNSAT)
            elif self.model_name == 'putinar':
                model = Putinar(self.program_variables, LHS=pair[0], RHS=pair[1],
                                max_d_for_sat=self.max_d_of_SAT, max_d_for_unsat=self.max_d_of_UNSAT,
                                max_d_for_unsat_strict=self.max_d_of_strict, max_d_for_new_var=self.degree_of_generated_var)
            else:
                print("no such model")
                return
            new_dnf = []
            if self.get_SAT:
                new_dnf.append(model.get_SAT_constraint())
            if self.get_UNSAT:
                new_dnf.append(model.get_UNSAT_constraint(need_strict=False))
            if self.get_strict:
                new_dnf.append(model.get_UNSAT_constraint(need_strict=True))
            all_constraint.append(DNF(new_dnf))
        return all_constraint

    def run_on_solver(self, solver_name='z3', solver_path=None, core_iteration_heuristic=False,
                      constant_heuristic=False, real_values=True
                      ):

        all_constraint = self.get_constraints()
        if solver_name == 'gurobi':
            check_constraints(all_constraint)
            return
        if solver_path is None:
            solver_path = Constant.default_path[solver_name]

        values_of_variable = {}
        if constant_heuristic and (self.get_SAT ^ self.get_UNSAT ^ self.get_strict) and (not (self.get_SAT and self.get_UNSAT and self.get_UNSAT)):
            all_constraint = PositiveModel.remove_equality_constraints(all_constraint)
        if core_iteration_heuristic:
            all_constraint = self.core_iteration(all_constraint, solver_path=solver_path,
                                                 real_values=real_values)


        solver_option = Constant.options[solver_name]

        names = ''
        for var in self.template_variables:
            if not (var in values_of_variable.keys()):
                names = names + ' ' + str(var)

        names = names.strip()
        output_command = '\n(check-sat)\n' + \
                         f'(get-value({names}))\n'

        f = open("checking.txt", "w")
        f.write(solver_option + Solver.smt_declare_variable_phase(all_constraint, real_values) + '\n' +
                Solver.convert_constraints_to_smt_format(all_constraint) + output_command
                )
        f.close()
        output = subprocess.getoutput(f'{solver_path} {Constant.command[solver_name]} checking.txt')
        is_sat = output.split('\n')[0]
        values = '\n'.join(output.split('\n')[1:])[1:-1].strip()
        print("here : ", is_sat)
        for line in values.split('\n'):
            line = line.strip()
            line = line[1:-1].strip()
            var_id = int(line.split(' ')[0].split('_')[-1])
            var_value = ' '.join(line.split(' ')[1:])
            for temp_var in self.template_variables:
                if temp_var.id == var_id:
                    values_of_variable[temp_var] = var_value
                    break

        for var in values_of_variable.keys():
            print(var, " : ", values_of_variable[var])

    @staticmethod
    def get_equality_constraint(all_constraint: [CoefficientConstraint]):
        for dnf in all_constraint:
            for literal in dnf.literals:
                for constraint in literal:
                    if constraint.is_equality():
                        return constraint
        return None

    @staticmethod
    def remove_equality_constraints(all_constraint: [CoefficientConstraint]):

        while True:
            equality_constraint = PositiveModel.get_equality_constraint(all_constraint)
            if equality_constraint is None:
                break
            amount = 0
            if len(equality_constraint.coefficient.elements) == 1:
                variable = equality_constraint.coefficient.elements[0].variables[0]
            else:
                element1 = equality_constraint.coefficient.elements[0]
                element2 = equality_constraint.coefficient.elements[1]
                if len(element1.variables) == 1:
                    variable = element1.variables[0]
                    if element2.constant == 0:
                        amount = 0
                    else:
                        amount = -element2.constant / element1.constant
                else:
                    variable = element2.variables[0]
                    if element1.constant == 0:
                        amount = 0
                    else:
                        amount = -element1.constant / element2.constant

            for dnf in all_constraint:
                for literal in dnf.literals:
                    for constraint in literal:
                        for element in constraint.coefficient.elements:
                            if variable in element.variables:
                                element.variables.remove(variable)
                                element.constant = element.constant * amount
        return all_constraint

    def core_iteration(self, all_constraint, solver_path='./solver/z3',
                       saving_path='save_for_core_iteration_heuristic_temp.txt', real_values=True):
        template_variables = self.template_variables[:]
        unsat = True
        while unsat and len(template_variables) > 0:
            generated_constraint = []
            new_name = []
            for var in template_variables:
                generated_constraint.append(
                    DNF(
                        [[CoefficientConstraint(Coefficient([Element('1', [var])]), '=')]]
                    )
                )

                new_name.append('cons-' + var.name)

            input_of_solver = '(set-option :produce-unsat-cores true)\n'
            input_of_solver += (Solver.smt_declare_variable_phase(all_constraint, real_values))
            input_of_solver += (Solver.convert_constraints_to_smt_format(generated_constraint, new_name))
            input_of_solver += (Solver.convert_constraints_to_smt_format(all_constraint))
            input_of_solver += '\n(check-sat)\n(get-unsat-core)\n'
            f = open(saving_path, "w")
            f.write(input_of_solver)
            f.close()

            output = subprocess.getoutput(f"{solver_path} {saving_path}")

            sat = output.split()[0]
            core = output.replace('(', ' ').replace(')', ' ').split()[1:]

            os.remove(saving_path)
            if sat == 'sat':
                return generated_constraint + all_constraint
            for name in core:
                name = name.strip()[5:]
                for var in template_variables:
                    if var.name == name:
                        delete_var = var
                        break
                template_variables.remove(delete_var)
        return all_constraint