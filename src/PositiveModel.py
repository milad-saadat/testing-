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
    """ This class is the main class which gets some horn clause as input and find the constraints based on the given
    theorem and find the template value using the given solver.


    Attributes:
        paired_constraint ([]): list of horn clause constraint as pair of left hand side and right han side.
        template_variables ([UnknownVariable]): list of unknown variable used as template variables.
        program_variables ([UnknownVariable]): list of unknown variable used as program variables.
        model_name (str): name of the algorithm should be used to find the constraints.

        get_SAT (bool): should constraint for satisfactory added or not.
        get_UNSAT (bool): should constraint for unsatisfactory added or not.
        get_strict (bool): should constraint for unsatisfactory in strict form added or not.

        max_d_of_SAT (int) : maximum degree of monoids when finding sat constraints in handelman or putinar.
        max_d_of_UNSAT (int) : maximum degree of monoids when finding unsat constraints in handelman or putinar.
        max_d_of_strict (int) : maximum degree of monoids when finding unsat constraints in strict case in handelman or putinar.
        degree_of_generated_var (int) : degree of new variable that is generated for strict case in right hand side of equality in putinar.

        preconditions ([DNF]) : list of conditions that must be satisfied independent of the horn clauses
    """

    def __init__(self, template_variables_name: [str], program_variables_name: [str],
                 model_name: str, get_SAT: bool = True, get_UNSAT: bool = False, get_strict: bool = False,
                 max_d_of_SAT: int = 0, max_d_of_UNSAT: int = 0, max_d_of_strict: int = 0, degree_of_generated_var: int = 0,
                 preconditions:[DNF] = []
                 ):
        self.paired_constraint = []
        self.template_variables = []
        self.program_variables = []
        for name in template_variables_name:
            self.template_variables.append(UnknownVariable(name=name, type_of_var='template_var'))
        for name in program_variables_name:
            self.program_variables.append(UnknownVariable(name=name, type_of_var='program_var'))

        self.model_name = model_name
        self.get_SAT = get_SAT
        self.get_UNSAT = get_UNSAT
        self.get_strict = get_strict
        self.max_d_of_SAT = max_d_of_SAT
        self.max_d_of_UNSAT = max_d_of_UNSAT
        self.max_d_of_strict = max_d_of_strict
        self.degree_of_generated_var = degree_of_generated_var
        self.preconditions = preconditions

    def add_paired_constraint(self, lhs: DNF, rhs: DNF):
        """ add set of horn clause constraint for lhs => rhs

        :param lhs: DNF form of the left hand side of that should be added.
        :param rhs: DNF form of the right hand side of that should be added.

        """
        if len(rhs.literals) > 1:
            lhs = lhs & (-(DNF(rhs.literals[1:])))
            rhs = DNF([rhs.literals[0]])
        for literal in lhs.literals:
            for item in rhs.literals[0]:
                self.paired_constraint.append((literal, item))

    def __str__(self) -> str:
        """ convert PositiveModel to string.

            :return: string format of the class.
        """
        res = ''
        for pair in self.paired_constraint:
            for lhs_item in pair[0]:
                res += str(lhs_item) + '\n'
            res += '->\n'
            res += str(pair[1]) + '\n'
            res += '----------------------\n'
        return res

    def get_polynomial(self, poly_str:str) -> Polynomial:
        """ generate a polynomial from a given string based on the template and program variable in the class

        :param poly_str: input string that should be converted to a polynomial.
        :return: polynomial of the given string.
        """
        return convert_general_string_to_poly(poly_str, self.template_variables + self.program_variables,
                                              self.program_variables)

    def get_constraints(self) -> [DNF]:
        """ This function find the constraint for the list of the class's horn clause constraints based on the class configurations.

        :return: list of DNF form of constraint for each horn clause.
        """
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
                                max_d_for_unsat_strict=self.max_d_of_strict,
                                max_d_for_new_var=self.degree_of_generated_var)
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
        return all_constraint + self.preconditions

    def run_on_solver(self, solver_name: str = 'z3', solver_path: str = None, core_iteration_heuristic: bool = False,
                      constant_heuristic: bool = False, real_values: bool = True
                      ) -> (bool,dict):
        """ This function find the constraints for the clauses and run a solver with given configuration and find values for the template variables.

        :param solver_name: name of the solver.
        :param solver_path: a path to solver file if it is None it uses the default path.
        :param core_iteration_heuristic: a boolean that determines the core iteration heuristic should be applied or not.
        :param constant_heuristic: a boolean that determines the removing constant heuristic should be applied or not.
        :param real_values: a boolean that determines if the variables should be integer or real value.
        :return: a boolean that is true if it  is satisfiable and a dictionary from template variable to their value.
        """
        all_constraint = self.get_constraints()
        if solver_name == 'gurobi':
            gurobi_res = check_constraints(all_constraint)
            result_dictionary = {}
            for var in gurobi_res.key():
                if var in self.template_variables:
                    result_dictionary[var] = gurobi_res[var]
            return result_dictionary
        if solver_path is None:
            solver_path = Constant.default_path[solver_name]

        values_of_variable = {}
        if constant_heuristic and (self.get_SAT ^ self.get_UNSAT ^ self.get_strict) and (
                not (self.get_SAT and self.get_UNSAT and self.get_UNSAT)):
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
        if is_sat == 'unsat':
            return False, {}
        for line in values.split('\n'):
            line = line.strip()
            line = line[1:-1].strip()
            var_id = int(line.split(' ')[0].split('_')[-1])
            var_value = ' '.join(line.split(' ')[1:])
            for temp_var in self.template_variables:
                if temp_var.id == var_id:
                    values_of_variable[temp_var] = var_value
                    break
        result_dictionary = {}
        for var in values_of_variable.keys():
            result_dictionary[var] = values_of_variable[var]
        return True, result_dictionary

    @staticmethod
    def get_equality_constraint(all_constraint: [DNF]):
        """ given a list of constraints find a constraint that is in form "template variable" = "constant"

        :param all_constraint: list of the constraints
        :return: a equality constraint.
        """
        for dnf in all_constraint:
            for literal in dnf.literals:
                for constraint in literal:
                    if constraint.is_equality():
                        return constraint
        return None

    @staticmethod
    def remove_equality_constraints(all_constraint: [DNF]):
        """ remove the equality constraints in each DNF

        :param all_constraint: list of the constraints.
        :return: new list of constraints after the heuristic is performed.
        """
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
        """ perform the core iteration heuristic on set of constraints.

        :param all_constraint: list of the constraint that the heuristic should be applied on.
        :param solver_path: solver path for finding the core
        :param saving_path: path to a file for temporary saving the output of solver.
        :param real_values: a boolean that determines if the variables should be integer or real value.
        :return: list of constraint after performing the heuristic.
        """
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
