from pathlib import Path
from fractions import Fraction
from datetime import datetime,timezone
import hashlib,json,re,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/foundations-explorer-horizon-exact31-v1')
assert not OUT.exists();OUT.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=ROOT/'SafeLearning/primer-basics.html'
raw=source.read_text()
matches=re.findall(r'var T99 = (.*?), Ts = Math.ceil',raw)
assert len(matches)==1
expr=matches[0]
assert expr=='gm === 0 ? 1 : Math.ceil(Math.log(0.01) / Math.log(gm) - 1e-12)'
assert 'id="p0-g" min="0" max="0.995" step="0.005"' in raw
js=r'''const fs = require('fs');
const html = fs.readFileSync(process.argv[1], 'utf8');
const matches = [...html.matchAll(/var T99 = (.*?), Ts = Math.ceil/g)];
if (matches.length !== 1) throw new Error('expected one actual horizon expression');
const expr = matches[0][1];
const rows = [];
for (let numerator = 0; numerator <= 199; numerator++) {
  const gm = Number((numerator / 200).toFixed(3));
  const T99 = eval(expr);
  rows.push({numerator, denominator:200, actual_admitted_value:gm, actual_horizon:T99});
}
process.stdout.write(JSON.stringify({actual_source_expression:expr, rows}));'''
cmd=['node','-e',js,str(source)]
started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
actual=subprocess.run(cmd,cwd=ROOT,capture_output=True)
elapsed=time.monotonic()-t;finished=datetime.now(timezone.utc).isoformat()
rawlog=OUT/'actual-original-node-horizon-output.json'
rawlog.write_bytes(actual.stdout)
stderr=OUT/'actual-original-node-stderr.log';stderr.write_bytes(actual.stderr)
assert actual.returncode==0
d=json.loads(actual.stdout);assert d['actual_source_expression']==expr
assert len(d['rows'])==200
checks=[]
for row in d['rows']:
 s=row['numerator'];T=row['actual_horizon']
 assert type(T) is int and T>=1
 gamma=Fraction(s,200);epsilon=Fraction(1,100)
 assert gamma**T<=epsilon
 assert gamma**(T-1)>epsilon
 checks.append({**row,'exact_rational_power_at_horizon_le_one_percent':True,
  'exact_rational_power_at_preceding_integer_gt_one_percent':True})
result={'status':'passed_actual_extracted_JS_horizon_expression_against_independent_exact_rational_thresholds',
 'source':{'file':str(source),'sha256':sha(source)},'actual_command':cmd,
 'actual_workdir':str(ROOT),'actual_exit_code':actual.returncode,
 'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':elapsed,
 'raw_stdout':{'file':str(rawlog),'sha256':sha(rawlog)},
 'raw_stderr':{'file':str(stderr),'sha256':sha(stderr)},
 'actual_source_expression':expr,'admitted_slider_domain':'gamma=s/200, s integer0..199; HTML min0/max.995/step.005.',
 'exact_reference':'Independent Python Fraction powers at both adjacent integer horizons; threshold exactly1/100.',
 'all200_exact_admitted_horizons_verified':True,'individual_checks':checks,
 'Lean_proof_or_generic_float_error_bound_claimed':False,'no_current_or_PUB_or_browser_writes':True,
 'coverage_complete':False}
target=OUT/'actual-extracted-JS-one-percent-horizons-all200-exact-reference-v1.json'
target.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'result':{'file':str(target),'sha256':sha(target)},'cases':len(checks),
 'maximum_actual_horizon':max(x['actual_horizon'] for x in checks),'actual_node_exit_code':actual.returncode}))
