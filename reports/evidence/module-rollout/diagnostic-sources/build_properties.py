import sys,subprocess
sys.path.insert(0,'experiments/kl-for-mathlib')
from validate import serial_environment
subprocess.run(['lake','--no-build','build','Mathlib'],cwd='experiments/kl-for-mathlib',env=serial_environment(),check=True)
subprocess.run(['lake','build','ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties'],cwd='experiments/kl-for-mathlib',env=serial_environment(),check=True)
