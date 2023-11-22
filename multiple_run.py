import sys
import time
import subprocess

#subprocess.run(["ls"])
from os import listdir
from os.path import isfile, join
fileName = './inputs/'
onlyfiles = [f for f in listdir(fileName) if isfile(join(fileName, f))]

index=0
for file in sorted(onlyfiles):
	for solver_name in ['mathsat', 'z3', 'bclt'] :
		index+=1
		print(str(index)+": "+file)
		output_name = file + "_"+solver_name+ '.out'
		script = f"""#!/bin/bash
#
#-------------------------------------------------------------
#running a shared memory (multithreaded) job over multiple CPUs
#-------------------------------------------------------------
#
#SBATCH --job-name={sys.argv[1]}-{file}
#SBATCH --output={sys.argv[1]}/{output_name}
#
#Number of CPU cores to use within one node
#SBATCH -c 1
#
#Define the number of hours the job should run. 
#Maximum runtime is limited to 10 days, ie. 240 hours
#SBATCH --time=00:30:00
#
#Define the amount of RAM used by your job in GigaBytes
#In shared memory applications this is shared among multiple CPUs
#SBATCH --mem=6G
#
#Pick whether you prefer requeue or not. If you use the --requeue
#option, the requeued job script will start from the beginning, 
#potentially overwriting your previous progress, so be careful.
#For some people the --requeue option might be desired if their
#application will continue from the last state.
#Do not requeue the job in the case it fails.
#SBATCH --no-requeue
#
#Do not export the local environment to the compute nodes
#SBATCH --export=NONE
unset SLURM_EXPORT_ENV
#
#Set the number of threads to the SLURM internal variable
export OMP_NUM_THREADS=$SLURM_CPUS_PER_TASK
#
#load the respective software module you intend to use
#
module load gmp/6.2.1

#run the respective binary through SLURM's srun


python main.py ./{fileName}{file} {solver_name}/
	"""

		f = open("tmp_run", "w")
		f.write(script)
		f.close()
		subprocess.run(["sbatch", "tmp_run"])
		time.sleep(0.1)
		
