import glob
import os
import shutil
import subprocess
import sys

root_dir = os.path.dirname(os.path.abspath(__file__))
tool = root_dir + "/bin/tlc-ian.jar"
tlc = root_dir + "/bin/tla2tools.jar"

def write(name, contents):
    f = open(name, "w")
    f.write(contents)
    f.close()

def create_err_trace(txt):
    lines = txt.split("\n")
    keep = []
    capture = False
    for l in lines:
        if ("Error:" in l):
            capture = True
        if ("distinct states found" in l):
            capture = False
        if (capture and "errCounter" not in l):
            keep.append(l)
    return "\n".join(keep)

def verify(spec, cfg, cust):
    # run model checking alg
    # use subprocess.call to send the output to stdout
    cmd_args = ["java", "-Xmx25g", "-jar", tool, "--verif", spec, cfg]
    if cust:
        cmd_args.append("--sc")
    retcode = subprocess.call(cmd_args)

    if (retcode == 99):
        replay_args = ["java", "-jar", tlc, "-deadlock", "ErrTrace.tla"]
        replay = subprocess.run(replay_args, capture_output=True, text=True)
        replay_out = replay.stdout
        if ("Error:" in replay_out):
            err_trace = create_err_trace(replay_out)
            print("Here is the error trace:\n")
            print(err_trace)
        else:
            print("Could not confirm the violating trace in the TLA+ spec; this is a bug in the tool.")

def run():
    if (len(sys.argv) < 3 or len(sys.argv) > 4):
        print("usage: verify.py [--cust] <file.tla> <file.cfg>")
        return
    if (len(sys.argv) == 4 and sys.argv[3] != "--cust"):
        print("usage: verify.py [--cust] <file.tla> <file.cfg>")
        return

    spec = sys.argv[1]
    cfg = sys.argv[2]
    cust = len(sys.argv) == 4 and sys.argv[3] == "--cust"

    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"

    #shutil.copyfile(spec, "out/"+spec)
    #shutil.copyfile(cfg, "out/"+cfg)
    for filename in glob.glob(os.path.join(orig_dir, '*.*')):
        shutil.copy(filename, dest_dir)

    os.chdir("out")
    verify(spec, cfg, cust)
    os.chdir(orig_dir)

run()
