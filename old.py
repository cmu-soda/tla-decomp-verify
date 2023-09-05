import os
import shutil
import subprocess
import sys

tlc_ian = "/Users/idardik/Documents/CMU/tla-robustness-src/bin/tlc-ian.jar"
alg_tool = "/Users/idardik/Documents/CMU/tolerance-permissiveness/LTS-Robustness/bin/LTS-Robustness.jar"

def write(name, contents):
    f = open(name, "w")
    f.write(contents)
    f.close()

def verify(spec, cfg):
    # hack for now
    write("no_invs.cfg", "SPECIFICATION Spec")
    
    # run decomp alg, get the files it produced
    cmd_args = ["java", "-jar", tlc_ian, "--decomp", spec, cfg]
    subprocess.run(cmd_args)
    decomp_iters = [int(f[1]) for f in os.listdir() if f[0] == "A"]
    num_iters = max(decomp_iters)
    
    # create the FSP safety property
    cmd_args = ["java", "-jar", tlc_ian, "--wa", "A1.tla", cfg]
    result = subprocess.run(cmd_args, text=True, capture_output=True)
    write("prop.fsp", result.stdout)

    # convert TLA+ modules to FSP
    fsp_files = []
    for i in range(1, num_iters+1):
        tla = "A" + str(i) + ".tla"
        fsp = "A" + str(i) + ".fsp"
        fsp_files.append(fsp)
        cmd_args = ["java", "-jar", tlc_ian, "--to-fsp", tla, "no_invs.cfg"]
        result = subprocess.run(cmd_args, text=True, capture_output=True)
        print(result.stderr)
        write(fsp, result.stdout)
    tla = "B" + str(num_iters) + ".tla"
    fsp = "B" + str(num_iters) + ".fsp"
    fsp_files.append(fsp)
    cmd_args = ["java", "-jar", tlc_ian, "--to-fsp", tla, "no_invs.cfg"]
    result = subprocess.run(cmd_args, text=True, capture_output=True)
    print(result.stderr)
    write(fsp, result.stdout)
    
    # run model checking alg
    # subprocess.call is like unix's exec
    cmd_args = ["java", "-jar", alg_tool, "prop.fsp"] + fsp_files
    subprocess.call(cmd_args)

def run():
    if (len(sys.argv) != 3):
        print("usage: verify.py <file.tla> <file.cfg>")
        return

    spec = sys.argv[1]
    cfg = sys.argv[2]

    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    shutil.copyfile(spec, "out/"+spec)
    shutil.copyfile(cfg, "out/"+cfg)
    os.chdir("out")
    verify(spec, cfg)
    os.chdir(orig_dir)

run()
