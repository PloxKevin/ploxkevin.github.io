from pathlib import Path
import hashlib
import json
import re

root = Path('/home/oxrexkevin/SafetyBased')
source = root / 'SafeLearning/landscape.html'
out = Path('/tmp/modules-landscape-explorer-independent-evidence19-v1')
out.mkdir(exist_ok=False)
raw = source.read_bytes()
html = raw.decode()
marker = '    // ===== Constraint Semantics Explorer =====\n'
start = html.index('    (function(){', html.index(marker) + len(marker))
end = html.index('    })();', start) + len('    })();')
iife = html[start:end]
(out / 'landscape-source.html').write_bytes(raw)
(out / 'explorer-original.js').write_text(iife)
nodes = {}
for match in re.finditer(r'<([A-Za-z0-9]+)\b([^>]*)>', html):
    attrs = dict(re.findall(r'([A-Za-z0-9_-]+)="([^"]*)"', match[2]))
    if 'id' in attrs and attrs['id'].startswith('ls-ce-'):
        nodes[attrs['id']] = {'tag': match[1], 'attributes': attrs}
(out / 'dom-spec.json').write_text(json.dumps(nodes, indent=2) + '\n')
draw_marker = '        // ---- plot 1: trajectories'
trace = """        globalThis.__ceTrace = {k:k,sigma:sig,T:T,alpha:a,budget:d,delta:del,
          seedNo:seedNo,prngSeed:20260929+seedNo*7919,N:N,TMAX:TMAX,
          analyticEN:EN,stationarySD:sInf,stationaryTail:pInf,sampleMeanCount:Jc,
          sampleMeanSE:seJ,violatingEpisodes:nv,jointEstimate:pv,jointSE:sePv,
          sampleCVaR:cv,sampleVaR:va,maxExcursion:zmax,meanExcursion:zmean,
          zeroBudgetFails:zeroBudgetFails,cmdpPass:okC,chanceSamplePass:okP,
          riskSamplePass:okR,hardSamplePass:okH,Ns:Ns,Zs:Zs,trajs:S.trajs};
"""
api_marker = "      ['ls-ce-k','ls-ce-sig','ls-ce-T','ls-ce-alpha','ls-ce-d','ls-ce-delta'].forEach"
api = """      globalThis.__ceAPI = {Q:Q,exactEN:exactEN,noise:noise,simulate:simulate,
        cvar:cvar,varA:varA,fp:fp,mulberry32:mulberry32,gauss:gauss};
"""
assert iife.count(draw_marker) == 1 and iife.count(api_marker) == 1
instrumented = iife.replace(draw_marker, trace + draw_marker).replace(api_marker, api + api_marker)
(out / 'explorer-instrumented.js').write_text(instrumented)
record = {'source': str(source), 'source_sha256': hashlib.sha256(raw).hexdigest(),
    'source_bytes': len(raw), 'iife_first_line': html[:start].count('\n')+1,
    'iife_last_line': html[:end].count('\n')+1,
    'original_iife_sha256': hashlib.sha256(iife.encode()).hexdigest(),
    'instrumented_sha256': hashlib.sha256(instrumented.encode()).hexdigest(),
    'instrumentation': 'Two insertions only: record existing local draw values; expose existing local functions. No algorithm, inputs, PRNG, N or TMAX edits.',
    'dom_nodes': sorted(nodes), 'live_source_written': False}
(out / 'extraction-record.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record))
