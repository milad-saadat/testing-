import sys
import time
import subprocess

#subprocess.run(["ls"])
import os
fileName = sys.argv[1]
base=os.path.basename(fileName)
config=f"configs/{fileName}"


script = f"""#!/bin/bash
#
#-------------------------------------------------------------
#running a shared memory (multithreaded) job over multiple CPUs
#-------------------------------------------------------------
#
#SBATCH --job-name={base}
#SBATCH --output=outputs/{fileName}
#
#Number of CPU cores to use within one node
#SBATCH -c 1
#
#Define the number of hours the job should run. 
#Maximum runtime is limited to 10 days, ie. 240 hours
#SBATCH --time=01:00:00
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
pip install numpy

#run the respective binary through SLURM's srun


./polyHorn -smt {fileName} {config}
	"""

f = open("tmp_run", "w")
f.write(script)
f.close()
subprocess.run(["sbatch", "tmp_run"])
time.sleep(0.1)
		
