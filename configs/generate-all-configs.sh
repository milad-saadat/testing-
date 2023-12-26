cd ..
# for x in benchmarks/RevTerm/all/*; do
#     python3 configs/single-config.py $x farkas 1 mathsat int > configs/int/$x;
#     python3 configs/single-config.py $x farkas 1 mathsat real > configs/real/$x;
#     echo $x;
# done 

# for x in benchmarks/RevTerm/best_config/*; do
#     python3 configs/single-config.py $x farkas 1 mathsat int > configs/int/$x;
#     python3 configs/single-config.py $x farkas 1 mathsat real > configs/real/$x;
#     echo $x;
# done
x="benchmarks/RevTerm/best_config/DoubleNeg.c.out"
python3 configs/single-config.py $x putinar 2 z3 int > configs/int/$x;
python3 configs/single-config.py $x putinar 2 z3 real > configs/real/$x;
x="benchmarks/RevTerm/best_config/ComplInterv.c.out"
python3 configs/single-config.py $x putinar 2 z3 int > configs/int/$x;
python3 configs/single-config.py $x putinar 2 z3 real > configs/real/$x;
x="benchmarks/RevTerm/best_config/Singapore_v2_false-termination.c.out"
python3 configs/single-config.py $x farkas 1 z3 int > configs/int/$x;
python3 configs/single-config.py $x farkas 1 z3 real > configs/real/$x;


# for x in benchmarks/Termination/linear/*; do 
#     python3 configs/single-config.py $x farkas 1 mathsat int > configs/int/$x;
#     python3 configs/single-config.py $x farkas 1 mathsat real > configs/real/$x;
#     echo $x;
# done

# for x in benchmarks/Termination/poly/*; do 
#     python3 configs/single-config.py $x putinar 2 mathsat int > configs/int/$x;
#     python3 configs/single-config.py $x putinar 2 mathsat real > configs/real/$x;
#     echo $x;
# done
