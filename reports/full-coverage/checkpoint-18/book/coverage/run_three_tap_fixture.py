#!/usr/bin/env python3
"""Run the explicitly scoped exact-rational random-kernel convolution fixture."""
from fractions import Fraction
from random import Random
from pathlib import Path
import json,hashlib,datetime
seed=126
rng=Random(seed)
cin,cout,horizon=3,2,40
kernels=[[[Fraction(rng.randrange(-20,21),8) for _ in range(cin)] for _ in range(cout)] for _ in range(3)]
bias=[Fraction(rng.randrange(-10,11),8) for _ in range(cout)]
inputs=[[Fraction(rng.randrange(-20,21),8) for _ in range(cin)] for _ in range(horizon)]
previous=[Fraction(0)]*cin
twice_previous=[Fraction(0)]*cin
comparisons=[]
for time in range(horizon):
 realization=[bias[row]+sum(kernels[0][row][col]*inputs[time][col]+kernels[1][row][col]*previous[col]+kernels[2][row][col]*twice_previous[col] for col in range(cin)) for row in range(cout)]
 direct=[bias[row]+sum(kernels[delay][row][col]*(inputs[time-delay][col] if time>=delay else 0) for delay in range(3) for col in range(cin)) for row in range(cout)]
 assert realization==direct
 comparisons.extend(abs(a-b) for a,b in zip(realization,direct))
 twice_previous=previous
 previous=inputs[time]
fixture={'seed':seed,'channels_in':cin,'channels_out':cout,'horizon':horizon,'kernels':[[[str(x) for x in row] for row in k] for k in kernels],'bias':list(map(str,bias)),'inputs':[[str(x) for x in row] for row in inputs]}
report={'status':'passed_actual_exact_rational_random_kernel_fixture','generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'arithmetic':'Python fractions.Fraction, exact rationals','fixture':fixture,'checked_output_coordinates':len(comparisons),'maximum_absolute_difference':str(max(comparisons)),'actual_exit_code':0,'limits':['This finite executed fixture is empirical evidence. Universality over all time indices and field-valued kernels is established separately by the actual Lean state/output theorems.','No binary floating-point rounding pipeline is asserted.']}
report['script']='book/coverage/run_three_tap_fixture.py';report['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
p=Path(__file__).resolve().parent/'checks/modules-three-tap-random-fixture-v2.json';p.write_text(json.dumps(report,indent=2)+'\n');print('Actual exact-rational random-kernel fixture passed: 40 times x2 output coordinates; maximum difference0.');print(hashlib.sha256(p.read_bytes()).hexdigest())
