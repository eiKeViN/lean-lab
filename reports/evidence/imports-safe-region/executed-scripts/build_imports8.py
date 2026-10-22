from pathlib import Path
import sys,json,subprocess
p=Path('/workspace/lean-lab/experiments/kl-for-mathlib');sys.path.insert(0,str(p));from validate import serial_environment
modules=[f[:-5].replace('/','.') for f in json.load(open('/workspace/lean-lab/results/imports-safe/candidates.json'))]
subprocess.run(['lake','--no-build','build','Mathlib'],cwd=p,env=serial_environment(),check=True)
subprocess.run(['lake','build',*modules],cwd=p,env=serial_environment(),check=True)
