#!/usr/bin/env python3
"""Build one stored topological prefix with the maintained serial compiler gate."""
import argparse,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'experiments/kl-for-mathlib'
sys.path.insert(0,str(P));from validate import serial_environment
from module_rollout import plan
p=argparse.ArgumentParser();p.add_argument('--limit',type=int);a=p.parse_args()
modules=plan()['topological_order'];modules=modules[:a.limit] if a.limit else modules
subprocess.run(['lake','--no-build','build','Mathlib'],cwd=P,env=serial_environment(),check=True)
raise SystemExit(subprocess.call(['lake','build',*modules],cwd=P,env=serial_environment()))
