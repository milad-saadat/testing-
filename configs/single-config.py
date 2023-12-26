import sys 
import os

name= sys.argv[1]  #os.path.basename(sys.argv[1])
theorem=sys.argv[2]     # farkas, putinar, handelman
degree = sys.argv[3]    # degree 
solver = sys.argv[4]    # z3, mathsat
varType = sys.argv[5]      # real/int
real=""

if varType=="int":
    real="false"
else:
    real="true"


print(f"""
{{
    "model_name": "{theorem}",
    "get_SAT": true,
    "get_UNSAT": false,
    "get_strict": false,
    "max_d_of_SAT": {degree},
    "max_d_of_UNSAT": 0,
    "max_d_of_strict": 0,
    "degree_of_generated_var": 0,
    "solver_name": "{solver}",
    "temp_path": "work/{name}.smt2",
    "solver_path": "default",
    "core_iteration_heuristic": false,
    "constant_heuristic": false,
    "real_values": {real}
}}
      """)