from pathlib import Path
from fractions import Fraction
import hashlib
import json
import math
import re

out = Path('/tmp/modules-landscape-explorer-independent-evidence19-v1')
source = Path('/home/oxrexkevin/SafetyBased/SafeLearning/landscape.html')
root = source.parent
html = source.read_text()
assets = []
for tag in re.finditer(r'<(?:script|link|img)\b[^>]*>', html):
    for attr in re.finditer(r'(?:src|href)="([^"]+)"', tag[0]):
        name = attr[1].split('#')[0].split('?')[0]
        if not name or name.startswith(('http:', 'https:', '//', 'data:')):
            continue
        file = (root / name).resolve()
        if file.is_file():
            assets.append({'reference': attr[1], 'file': str(file),
                'bytes': len(file.read_bytes()), 'sha256': hashlib.sha256(file.read_bytes()).hexdigest()})

def moments(k, sigma, goal, t):
    a = 1-k
    m = goal*(1-a**t)
    v = sigma**2 * sum(a**(2*i) for i in range(t))
    return m, v

def tail(m, v):
    return math.erfc(float((1-m)/math.sqrt(v))/math.sqrt(2))/2 if v else int(m>1)

def scenario(k, sigma, T, goal):
    terms = []
    for t in range(1,T+1):
        m,v=moments(k,sigma,goal,t)
        terms.append({'t':t,'mean_exact':str(m),'variance_exact':str(v),
            'mean':float(m),'variance':float(v),'sd':math.sqrt(v),
            'z':float((1-m)/math.sqrt(v)) if v else None,'math_erfc_tail':tail(m,v)})
    vinf = sigma**2/(k*(2-k))
    pinf = tail(goal,vinf)
    return {'settings_exact':{'k':str(k),'sigma':str(sigma),'T':T,'goal':str(goal)},
        'stationary_variance_exact':str(vinf),'stationary_variance':float(vinf),
        'stationary_sd':math.sqrt(vinf),'stationary_z':float((1-goal)/math.sqrt(vinf)) if vinf else None,
        'stationary_tail':pinf,'stationary_approx_count':T*pinf,
        'mean_violating_steps':math.fsum(x['math_erfc_tail'] for x in terms),'terms':terms}

exercise = scenario(Fraction(1,2),Fraction(1,10),40,Fraction(4,5))
defaults = scenario(Fraction(1,2),Fraction(7,100),40,Fraction(4,5))
def q(z): return math.erfc(z/math.sqrt(2))/2
lo,hi=8.0,8.5
for i in range(80):
    mid=(lo+hi)/2
    if 1-(1-q(mid))==0: hi=mid
    else: lo=mid
tails=[{'z':z,'math_erfc_tail':q(z),'rounded_cdf':1-q(z),'subtract_from_rounded_cdf':1-(1-q(z))}
    for z in [0,1,math.sqrt(3),6,8,8.2,8.3,9,20,38,38.4,38.45,38.5,39,96]]
record={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'assets_read_only_hashes':assets,'python_float_library':'Python math.erfc / host libm; not arbitrary precision and no Lean numeric proof',
    'moments_computed_with_exact_Fraction_inputs':True,'exercise':exercise,'defaults':defaults,
    'cancellation_threshold_for_forming_cdf_as_1_minus_math_erfc_tail':{'nonzero_lo':lo,'zero_hi':hi},'tail_checks':tails,
    'limitations':['Only moments are computed as exact rationals; sqrt, erfc, probability values use binary64 library execution.',
        'The cancellation threshold depends on how a CDF is approximated and rounded. This explicitly tests subtraction from 1-Q.',
        'A finite PRNG simulation is empirical execution evidence and cannot certify the true iid Gaussian joint law or exact joint probability.',
        'Literal equals signs adjoining rounded decimals do not express true real equalities.']}
(out/'numeric-crosscheck.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'exercise':{key:value for key,value in exercise.items() if key!='terms'},
    'selected_transients':[term for term in exercise['terms'] if term['t'] in (1,3,5,10)],
    'defaults_mean_violating_steps':defaults['mean_violating_steps'],
    'cancellation':record['cancellation_threshold_for_forming_cdf_as_1_minus_math_erfc_tail'],'tail_checks':tails},indent=2))
