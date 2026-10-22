#!/usr/bin/env python3
"""Scope shake's no-build preflight to the ready focused modules; never force/fix."""
from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'experiments/kl-for-mathlib'
modules=['ForMathlib.LinearAlgebra.CoordinateProjection','ForMathlib.LinearAlgebra.ConjugateRange',
'ForMathlib.LinearAlgebra.Dual.TransportPairing','ForMathlib.LinearAlgebra.Dual.Summand',
'ForMathlib.LinearAlgebra.TensorProduct.Coordinates','ForMathlib.LinearAlgebra.Quotient.Transport',
'ForMathlib.Algebra.Module.Projective.Range','ForMathlib.Algebra.Module.Submodule.ScaledImage',
'ForMathlib.Algebra.Module.Submodule.PiIdeal','ForMathlib.Order.Interval.Diamonds',
'ForMathlib.LinearAlgebra.Avoidance','ForMathlib.Algebra.Module.Free.ScalarDivisibility',
'ForMathlib.Algebra.Module.Cover.Local','ForMathlib.Algebra.Order.Field.RealScaling']
config=P/'lakefile.toml';before=config.read_bytes()
try:
 text=before.decode();old='defaultTargets = ["ForMathlib", "OAI"]'
 if text.count(old)!=1:raise RuntimeError('Unexpected default target configuration')
 config.write_text(text.replace(old,'defaultTargets = '+json.dumps(modules)))
 subprocess.run(['lake','--no-build','build',*modules],cwd=P,check=True)
 # Exit 1 can mean proposed changes. Raw status/output remain explicit.
 result=subprocess.run(['lake','shake',*modules],cwd=P)
 print('Scoped read-only shake status:',result.returncode)
finally:
 config.write_bytes(before)
assert config.read_bytes()==before
