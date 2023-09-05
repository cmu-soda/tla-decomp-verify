import glob
import os
import shutil
import subprocess
import sys

root_dir = os.path.dirname(os.path.abspath(__file__))
tool = root_dir + "/bin/tlc-ian.jar"

def write(name, contents):
    f = open(name, "w")
    f.write(contents)
    f.close()

def verify(spec, cfg):
    # run model checking alg
    # subprocess.call is like unix's exec
    cmd_args = ["java", "-Xmx25g", "-jar", tool, "--verif", spec, cfg]
    subprocess.call(cmd_args)

def run():
    if (len(sys.argv) != 3):
        print("usage: verify.py <file.tla> <file.cfg>")
        return

    spec = sys.argv[1]
    cfg = sys.argv[2]

    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"

    #shutil.copyfile(spec, "out/"+spec)
    #shutil.copyfile(cfg, "out/"+cfg)
    for filename in glob.glob(os.path.join(orig_dir, '*.*')):
        shutil.copy(filename, dest_dir)

    os.chdir("out")
    verify(spec, cfg)
    os.chdir(orig_dir)

run()
