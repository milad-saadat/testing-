import sys
from os import listdir
from os.path import isfile, join


def extract_time(line):
    tmp = line.split()[1]
    (minute, sec) = (tmp.split('m')[0], tmp.split('m')[1])
    minute = int(minute)
    sec = float(sec[:-1])
    return (minute * 60 + sec) * 1000


dir = sys.argv[1]
onlyfiles = [f for f in listdir(dir) if isfile(join(dir, f))]
onlyfiles = sorted(onlyfiles)

for file in onlyfiles:
    sat = False
    time = ""
    with open(f"{dir}/{file}", "r") as fr:
        x = fr.readlines()
        for line in x:
            if line[:3] == "sat":
                sat = True
            if "real" in line and sat:
                time = extract_time(line)
    print(f"{file}, {sat}, {time}")
    # break
