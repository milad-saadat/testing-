import gurobipy as gp
from gurobipy import GRB
from src.UnknownVariable import UnknownVariable


def check_constraints(all_constraint):
    all_variables = set()
    for constraint in all_constraint:
        for element in constraint.coefficient.elements:
            all_variables = all_variables.union(set([var for var in element.variables]))

    with gp.Env(empty=True) as env:
        env.setParam("WLSACCESSID", "a891a997-3fcf-4687-bdcf-5d0ce4ba00fe")
        env.setParam("WLSSECRET", "9dab956b-dc58-489c-be4e-87d5e61a4117")
        env.setParam("LICENSEID", 2398947)
        env.setParam("OutputFlag", 0)
        env.start()
        model = gp.Model(env=env)
        model.setParam("NonConvex", 2)

    dict_from_name_to_gpvar = {}

    for var in all_variables:
        dict_from_name_to_gpvar[str(var)] = model.addVar(name=str(var), vtype=GRB.CONTINUOUS)

    model.update()

    for constraint in all_constraint:
        gp_con = 0
        for element in constraint.coefficient.elements:
            new_cons = element.constant
            for var in element.variables:
                new_cons = new_cons * dict_from_name_to_gpvar[str(var)]
            gp_con = gp_con + new_cons
        if constraint.sign == '=':
            model.addConstr(gp_con == 0)
        elif constraint.sign == '>=':
            model.addConstr(gp_con >= 0)

    model.optimize()
    ret_value = GRB.OPTIMAL
    if ret_value != 2:
        print('not satisfied')
        return
    for name in dict_from_name_to_gpvar.keys():
        print(name, " : ", dict_from_name_to_gpvar[name].X)
