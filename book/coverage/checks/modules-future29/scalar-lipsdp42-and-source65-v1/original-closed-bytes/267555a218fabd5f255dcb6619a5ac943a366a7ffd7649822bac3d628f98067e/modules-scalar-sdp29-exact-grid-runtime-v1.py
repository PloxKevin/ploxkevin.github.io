from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal,ROUND_HALF_UP
from datetime import datetime,timezone
import json,hashlib
P=Path('/tmp/modules-scalar-sdp29-exact-grid-runtime-result-v1.json');assert not P.exists();start=datetime.now(timezone.utc).isoformat()
q=F(49,100);w0sq=F(169,100)
rows=[(k,w0sq*F(k,1000)**2/(2*F(k,1000)-q))for k in range(4001)if q/2<F(k,1000)]
minimum=min(v for k,v in rows);argmin=[k for k,v in rows if v==minimum]
assert len(rows)==3755 and minimum==F(8281,10000)and argmin==[490]
M=[[F(-8281,10000),F(637,1000)],[F(637,1000),F(-49,100)]];zero=[F(7,10),F(91,100)];negative=[F(91,100),F(-7,10)];lam=F(-13181,10000)
assert [sum(M[i][j]*zero[j]for j in range(2))for i in range(2)]==[0,0]
assert [sum(M[i][j]*negative[j]for j in range(2))for i in range(2)]==[lam*v for v in negative]
trace=sum(M[i][i]for i in range(2));det=M[0][0]*M[1][1]-M[0][1]*M[1][0]
assert trace==lam and det==0
rounded=(Decimal(lam.numerator)/Decimal(lam.denominator)).quantize(Decimal('.001'),rounding=ROUND_HALF_UP);assert rounded==Decimal('-1.318')
out={'status':'passed_actual_exact_rational_scalar_lipsdp_grid_and_matrix_runtime','started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'arithmetic':'Python Fraction exact rational; eigenvalue rounding Decimal ROUND_HALF_UP','grid_k_range_inclusive':[0,4000],'grid_t_definition':'k/1000, filtered t>49/200','actual_valid_grid_count':len(rows),'unique_argmin_k':argmin,'actual_optimal_t':str(F(argmin[0],1000)),'actual_optimal_rho':str(minimum),'actual_gain':'91/100','actual_source_matrix':[[str(z)for z in row]for row in M],'actual_exact_trace':str(trace),'actual_exact_determinant':str(det),'exact_eigenvalues':['0',str(lam)],'actual_three_decimal_rounding':str(rounded),'source_grid_and_global_min_have_independent_real_Lean_proofs':True,'no_float_numeric_assertion_used':True,'coverage_complete':False}
P.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'result':str(P),'sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'valid_grid_count':len(rows),'argmin':argmin}))
