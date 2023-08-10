class Constant:
    """This class consist of some constant dictionaries which are used for configuration of the solvers.

    """
    options = {
        'z3': '(set-option :print-success false)\n' + \
              '(set-option :produce-models true)\n'
        ,
        'mathsat': '(set-option :print-success false)\n' + \
                   '(set-option :produce-models true)\n'
        ,
        'bclt': '(set-option :print-success false)\n' +\
                '(set-option :produce-models true)\n'+\
                '(set-option :produce-assertions true)\n'+\
                '(set-logic QF_NIA)\n'

    }

    default_path = {
        'z3': 'solver/z3',
        'mathsat': 'solver/mathsat',
        'bclt': 'solver/bclt'
    }

    command = {
        'z3': '',
        'mathsat': '',
        'bclt': '--file '
    }
