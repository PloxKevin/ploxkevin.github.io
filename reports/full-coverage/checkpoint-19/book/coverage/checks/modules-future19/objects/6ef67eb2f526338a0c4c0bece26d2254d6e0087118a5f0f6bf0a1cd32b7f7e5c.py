from pathlib import Path
import json,hashlib,datetime,copy
R=Path('/home/oxrexkevin/SafetyBased');C=R/'book/coverage/checks'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
aliases=J(C/'modules-future19/path-aliases33-v3.json')['aliases']
def canonical(s):return aliases.get(s,{}).get('path',s)
def P(s):
    s=canonical(s);p=Path(s);return p if p.is_absolute()else R/p
ip='book/coverage/inventory-after-correction44.json';assert H(R/ip)=='29f83fd5409b98de5d82cdc3164eca87311870db12289cf2c63b8a2aaf717c6e'
inv=J(R/ip);es={x['key']:x for x in inv['exercises']};us={x['key']:x for x in inv['material_source_units']}
specs=[
 ('design-hard3','/tmp/modules-design-hard3-truncation-source-components-review19-v1.json',
  'lipschitz-by-design.html#practice-hard-3',None,
  'Fresh complete corrected question, prerequisite pointer, hint and all three worked steps read. The true skew exponential is an orthogonal rotation; actual S2 Gram gives norm sqrt(1.0004)>1. The rational remainder1/750 is correctly displayed as approximately.00133333; the exact triangle bound and slightly smaller rounded bound are each justified independently. Every ten-layer composition with actual1-Lipschitz activations has both printed product bounds and certified roundings; zero and identity activations substantiate the reduction/absence-of-unit-gain-guarantee statements.'),
 ('gosafe-noisy65','/tmp/modules-gosafe-noisy6-5-source-components-review-v1.json',
  'gosafe.html::exercise-19',None,
  'Fresh complete corrected6.5 question and all three answer parts read. Actual closed-ball equivalences give radii.20/.10 and noisy.18/.08. Genuine Euclidean distances and margins are now qualified approximations, both balls fail, both margins are positive and the first is the attained larger margin. Current plus stored measurement errors require the full.02 allowance; their legitimate independent good events give one-comparison confidence1-delta2. Whole-run comparisons require the separately proved finite failure union together with the GP event, exactly as the source cautions.'),
 ('gosafe-toy701','/tmp/modules-gosafe-toy-material-components-source-review19-v7.json',
  None,['gosafe.html::node-701'],
  'Fresh whole corrected equilibrium paragraph read against the actual source Euler definitions and full proofs. The exact fixed point, subtracted recurrence, closed form and source ratio bounds match. Arbitrary starts approach monotonically or antitonically; nonarrival is explicitly restricted to unequal initial/equilibrium states, while equal states stay fixed. Genuine bounded real supremum and infimum arguments give sup abs trajectory=max(abs initial,equilibrium) and true all-horizon margin1 minus that maximum. No explorer, GP or continuous-ODE safety theorem is inferred from this discrete Euler paragraph.')]
cm=J(R/'reports/full-coverage/checkpoint-18-manifest.json');prot={}
for f,d in cm['proof_files'].items():prot[f]=d['sha256'];prot.update(d['evidence_sha256'])
for f,h in prot.items():assert H(R/f)==h
for f,h in cm['frozen_inputs_sha256'].items():assert H(R/cm['snapshot']/f)==h
for label,oldp,ek,keys,reason in specs:
    old=J(P(oldp));proofs=copy.deepcopy(old['proof_source_sha256']);groups=copy.deepcopy(old['components'])
    if label=='gosafe-toy701':
        prefixes=['verification/lean/SafeLearning/CompleteModulesGoSafeToyAffine.lean',
                  'verification/lean/SafeLearning/CompleteModulesGoSafeToyTrajectoryConsequences.lean']
        proofs={p:h for p,h in proofs.items()if p in prefixes}
        groups=[c for c in groups if c['component_id'] in ['actual-euler-recursion-fixedpoint-closedform-and-infimum','actual-arbitrary-start-monotonicity-nonarrival-and-absolute-supremum']]
    for f,h in proofs.items():assert H(R/f)==h
    evidence=[]
    for row in old['actual_standalone_evidence']:
        p=row['compiler_manifest'];d=J(P(p))
        if d['source']not in proofs:continue
        assert H(P(p))==row['compiler_manifest_sha256'] and d['exit_code']==0
        assert d.get('source_sha256_before',d.get('sha256_before'))==d.get('source_sha256_after',d.get('sha256_after'))==proofs[d['source']]
        lp=d['log'];assert H(P(lp))==d['log_sha256']
        evidence.append({'compiler_manifest':canonical(p),'compiler_manifest_sha256':H(P(p)),
                         'actual_exit_code':0,'record':copy.deepcopy(d),
                         'canonical_raw_log':canonical(lp),'canonical_raw_log_sha256':H(P(lp)),
                         'actual_raw_log_bytes':P(lp).stat().st_size})
    for c in groups:
        c['review_status']='approved_precise_source_component';c['material_status']='proved';c['missing_clauses']=[]
        c['id']=c['component_id'];c['per_unit_reason']=c.get('per_component_reason',reason)
        if c['component_id']=='true-rational-remainder-and-valid-looser-layer-bound':
            c['per_unit_reason']='Actual rational remainder1/750 has the certified eight-place approximation and strict non-equality. The corrected exact triangle bound1+1/750 and separately valid rounded1.00133333 norm bound match the actual proofs.'
        if c['component_id']=='actual-planar-trigger-optimal-backup-and-roundings':
            c['per_unit_reason']='Actual distances sqrt(17/400),sqrt(1/80), actual margins and IsGreatest first-backup choice have the certified three-place approximations. Corrected expressions use genuine norms and qualify the irrational decimal displays.'
    if label=='gosafe-toy701':
        hyps=['Actual source real Euler map with step1/400, gain3+5a2 for a2 in[0,1], nonnegative source reference(4/5)*(1+cos(4*pi*a1)), constant disturbance3/5 and margin1-abs x.',
              'The source ratio lies in[391/400,99/100], hence is strictly positive and less than1; equilibrium is positive. The start is arbitrary real; nonarrival uses exactly initial!=equilibrium, and equality is the fixed trajectory case.',
              'Supremum and infimum are genuine nonempty bounded real ranges over every natural time, with convergence used for possibly unattained limiting extrema.']
        for c in groups:c['hypotheses']=hyps
    else:hyps=list(dict.fromkeys(h for c in groups for h in c['hypotheses']))
    decl=sorted({n for c in groups for n in c['lean_declarations']})
    materials=[]
    if keys is None:keys=[x['source_unit_key']for x in old['material_units']]
    for key in keys:
        u=us[key];assert H(R/u['source'])==u['source_sha256']
        prior=next(x for x in old['material_units']if x['source_unit_key']==key)
        nonformal=prior.get('material_status')=='not_a_formal_claim' or prior.get('review_status') in ['approved_nonformal_material','approved_nonformal_source_unit']
        materials.append({'source_unit_key':key,'unit_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],
          'source_text':u['source_text'],'line':u['line'],'locator':u['locator'],
          'review_status':'approved_nonformal_material'if nonformal else'approved_complete_source',
          'material_status':'not_a_formal_claim'if nonformal else'proved',
          'per_unit_reason':prior.get('per_unit_reason',prior.get('reason','Individually read prerequisite study pointer; no mathematical conclusion.'))if nonformal else reason,
          'hypotheses':[]if nonformal else hyps,'lean_declarations':[]if nonformal else decl,
          'reviewed_clauses':[]if nonformal else groups,'missing_clauses':[]})
    records=[]
    if ek:
        e=es[ek]
        records=[{'exercise_key':ek,'exercise_text_sha256':e['text_sha256'],'exercise_text':e['source_text'],
          'source_sha256':e['source_sha256'],'review_status':'approved_complete_source',
          'independent_whole_source_review_passed':True,'whole_exercise_approved':True,
          'reviewed_clauses':groups,'components':groups,'lean_declarations':decl,
          'hypotheses':hyps,'per_exercise_reason':reason,'missing_clauses':[]}]
    out={'schema_version':1,'status':'independent_fresh_corrected44_literal_source_review_passed',
      'reviewer':'/root/applied_next','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'inventory':ip,'inventory_sha256':H(R/ip),'source_sha256':{us[k]['source']:us[k]['source_sha256']for k in keys},
      'original_component_review':canonical(oldp),'original_component_review_sha256':H(P(oldp)),
      'original_reviewed_at_utc_preserved':old['reviewed_at_utc'],
      'historical_missing_clauses_preserved':copy.deepcopy(old['missing_clauses']),
      'proof_source_sha256':proofs,'actual_standalone_evidence':evidence,
      'components':groups,'records':records,'material_units':materials,'missing_clauses':[],
      'protected_selected490_source_and_evidence_paths_checked':len(prot),'frozen18_inputs_checked':len(cm['frozen_inputs_sha256']),
      'limits':['Fresh complete decisions apply only to the exact corrected44 literals individually read here. All historical review bodies/times/partial decisions and original actual compiler records remain unchanged.',
                'Compiler evidence is the existing genuine source-matched exit0 record with actual warning logs preserved. This review claims no new compilation, browser check or aggregate/kernel audit.',
                'No HTML, global inventory or owner ledger/helper/offer is written.']}
    if label=='gosafe-noisy65':out['primary_source_scope_check']=copy.deepcopy(old['primary_source_scope_check'])
    p=C/f'modules-{label}-corrected44-full-source-review19-v1.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
    print(str(p.relative_to(R)),H(p),len(materials))
