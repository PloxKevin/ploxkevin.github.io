from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, subprocess, tempfile
R=Path('/home/oxrexkevin/SafetyBased')
BASE='book/coverage/checks/future25-core'
V1='book/coverage/checks/root_close_checkpoint25_selection_plan_v1.py'
V2='book/coverage/checks/root_close_checkpoint25_selection_plan_v2.py'
OLD=BASE+'/checkpoint25-installed-owner-selection-plan-v1.json'
NEW=BASE+'/checkpoint25-installed-owner-selection-plan-v2.json'
REPORT=Path('/tmp/checkpoint25-plan-closer-independent-applied-review-v1.json')
assert not REPORT.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda n:{'file':n,'sha256':H(R/n)}
s1=(R/V1).read_text();s2=(R/V2).read_text()
oldline="    assert d['actual_exit_code']==0 and sha(d['log'])==d['log_sha256']"
newline="    exits = [d[k] for k in ('actual_exit_code','exit_code') if k in d]\n    assert exits and all(type(value) is int and value == 0 for value in exits)\n    assert sha(d['log']) == d['log_sha256']"
assert s1.count(oldline)==1 and s2.replace(newline,oldline)==s1
assert H(R/V1)=='304c6a57dc72c8e1f4b3ada8a1ceb38a3c24605379dc2161db922d148e106836'
assert H(R/V2)=='969b7eac54fcf33f5db1e06cd6394044f6574bbec64c9b2feb7cd7910aedab74'
compile(s2,V2,'exec')
helpers_before={n:H(R/n) for n in [V1,V2]}
inv='book/coverage/inventory-after-correction52.json'
invd=json.loads((R/inv).read_text());assert H(R/inv)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
selection=json.loads((R/'reports/full-coverage/checkpoint-24-selection.json').read_text())
assert len(selection['proof_files'])==1144
for row in selection['proof_files']:
    assert H(R/row['file'])==row['sha256'],row['file']
STEMS=['prepare-owner25-interface-request-execution-v1','prepare-owner25-live-interfaces-execution-v1','prepare-owner25-selection-plan-execution-v1']
FIX=[]
def fixture(label, mutate=None, expect=True, ver=V2, exit_fields=None):
    with tempfile.TemporaryDirectory(prefix='closer25-synthetic-') as tmp:
        f=Path(tmp)
        def put(n,b):
            p=f/n;p.parent.mkdir(parents=True,exist_ok=True)
            if isinstance(b,dict):b=(json.dumps(b,indent=2)+'\n').encode()
            elif isinstance(b,str):b=b.encode()
            p.write_bytes(b)
        def read(n):return json.loads((f/n).read_text())
        put(ver,(R/ver).read_bytes())
        retained=BASE+'/retained-original-peer.json';put(retained,{'synthetic_fixture':True,'reviewed_at_utc':'old-time','body':{'status':'pending','gaps':['retained exact']}})
        old={'status':'independently_reviewed_installed_owner25_selection_plan','created_at_utc':'synthetic-old-time','additional_frozen_inputs':{retained:{'sha256':H(f/retained),'scope':'prior evidence'}},'helpers_sha256':{'synthetic-original-helper.py':'old-hash'},'excluded_full_external_reference_sha256':[],'owner_math_body':{'review_time':'unchanged-time','declarations':['unchanged'], 'hypotheses':['unchanged'],'missing_clauses':['unchanged gap']},'synthetic_fixture':True}
        put(OLD,old)
        fields={'actual_exit_code':0} if exit_fields is None else exit_fields
        for stem in STEMS:
            log='reports/full-coverage/'+stem+'.log';put(log,'synthetic closure log '+stem+'\n')
            put('reports/full-coverage/'+stem+'.json',dict(fields,log=log,log_sha256=H(f/log),command=['synthetic','fixture'],started_at_utc='synthetic-start',finished_at_utc='synthetic-end',synthetic_fixture=True))
        for n in ['book/coverage/checks/pages24-config-helper-independent-modules-review-v2.json','book/coverage/checks/future24-core/pages24-config-independent-output-review-v1.json']:
            put(n,{'synthetic_fixture':True,'status':'placeholder for code testing only'})
        # Newly closed evidence is deliberately synthetic, and every helper run is rooted only here.
        if mutate:mutate(f,put,read)
        original_old=(f/OLD).read_bytes()
        cp=subprocess.run(['python3',str(f/ver)],cwd=f,capture_output=True,text=True)
        ok=cp.returncode==0
        assert ok==expect,(label,cp.returncode,cp.stdout,cp.stderr)
        assert (f/OLD).read_bytes()==original_old
        assert not (f/'reports/full-coverage/checkpoint-25-selection.json').exists() or label=='preexisting production selection'
        row={'label':label,'synthetic_fixture':True,'helper_version':ver,'observed_exit_code':cp.returncode,'expected_acceptance':expect}
        if ok:
            out=read(NEW);inverse=copy.deepcopy(out)
            for k in ['original_installed_owner_selection_plan_v1','entire_original_installed_owner_selection_plan_v1_body_and_time','closed_interface_and_plan_original_byte_aliases','plan_closure_prepared_at_utc']:inverse.pop(k)
            inverse['additional_frozen_inputs']=old['additional_frozen_inputs'];inverse['helpers_sha256']=old['helpers_sha256']
            assert inverse==old and out['entire_original_installed_owner_selection_plan_v1_body_and_time']==old
            catalog=read(BASE+'/root-closed-interface-plan-original-byte-aliases25-v1.json')
            assert len(catalog['aliases'])==6
            for a in catalog['aliases']:
                o=a['original'];c=a['immutable_original_byte_copy'];assert (f/o['file']).read_bytes()==(f/c['file']).read_bytes();assert H(f/o['file'])==o['sha256']==c['sha256']
            for n,r in out['additional_frozen_inputs'].items():assert H(f/n)==r['sha256']
            assert out['helpers_sha256'][ver]==H(f/ver)
            row.update(exact_original_plan_inverse=True,six_closed_aliases_byte_exact=True)
        else:
            # No new approved plan can result from any rejected case.
            if label!='preexisting output plan':assert not (f/NEW).exists()
            row['stderr_sha256']=hashlib.sha256(cp.stderr.encode()).hexdigest()
        FIX.append(row)
fixture('actual_exit_code integer zero')
fixture('exit_code integer zero',exit_fields={'exit_code':0})
fixture('both agreeing integer zero aliases',exit_fields={'actual_exit_code':0,'exit_code':0})
for label,fields in [('False actual alias',{'actual_exit_code':False}),('True actual alias',{'actual_exit_code':True}),('float zero',{'actual_exit_code':0.0}),('string zero',{'actual_exit_code':'0'}),('missing aliases',{}),('failure exit one',{'actual_exit_code':1}),('conflicting aliases',{'actual_exit_code':0,'exit_code':1}),('False secondary alias',{'actual_exit_code':0,'exit_code':False}),('null secondary alias',{'actual_exit_code':0,'exit_code':None}),('nonzero secondary',{'exit_code':2})]:fixture(label,expect=False,exit_fields=fields)
fixture('held v1 False bug demonstrated only synthetically',expect=True,ver=V1,exit_fields={'actual_exit_code':False})
# Repeat strict rejection at each of the three original record positions.
for i,stem in enumerate(STEMS):
    def mut(f,put,read,stem=stem):
        n='reports/full-coverage/'+stem+'.json';d=read(n);d['actual_exit_code']=False;put(n,d)
    fixture('False rejected at native position '+str(i),mut,False)
def logdrift(f,put,read):put('reports/full-coverage/'+STEMS[1]+'.log','changed synthetic rawlog')
fixture('rawlog drift rejected',logdrift,False)
def badhash(f,put,read):
    n='reports/full-coverage/'+STEMS[0]+'.json';d=read(n);d['log_sha256']='0'*64;put(n,d)
fixture('wrong declared rawlog hash',badhash,False)
fixture('preexisting production selection',lambda f,put,read:put('reports/full-coverage/checkpoint-25-selection.json',{}),False)
fixture('preexisting output plan',lambda f,put,read:put(NEW,{}),False)
def existingalias(f,put,read):(f/(BASE+'/root-closed-interface-plan-original-bytes25-v1')).mkdir()
fixture('preexisting archival alias directory',existingalias,False)
def oldstatus(f,put,read):
    d=read(OLD);d['status']='unreviewed';put(OLD,d)
fixture('unreviewed original plan status',oldstatus,False)
def olddrift(f,put,read):put(BASE+'/retained-original-peer.json',{'synthetic_fixture':True,'changed':True})
fixture('retained old evidence digest drift',olddrift,False)
def excluded(f,put,read):
    d=read(OLD);d['excluded_full_external_reference_sha256']=[H(f/(BASE+'/retained-original-peer.json'))];put(OLD,d)
fixture('explicitly excluded full external reference digest',excluded,False)
fixture('missing required prior actual config peer',lambda f,put,read:(f/'book/coverage/checks/pages24-config-helper-independent-modules-review-v2.json').unlink(),False)
for n,v in helpers_before.items():assert H(R/n)==v
for row in selection['proof_files']:assert H(R/row['file'])==row['sha256']
assert H(R/inv)==ref(inv)['sha256']== '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
out={'status':'passed_independent_unexecuted_checkpoint25_plan_closer_code_and_synthetic_fixtures','passed':True,'errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(V2),'helper_sha256':H(R/V2),'preserved_v1_helper':ref(V1),'exact_delta':'Only all-present exit aliases are changed to nonempty strict integer-zero validation; rawlog guard and every other operation match v1 byte-for-byte.','whole_code_scope':'Reads the original independently reviewed installed-owner plan, binds only three closed original wrapper/rawlog pairs, rehashes all added local evidence against explicit full-reference exclusions, preserves original entire body/time and verifies inverse before a distinct new plan write. Old plan bytes are immutable.','fixtures':FIX,'fixture_count':len(FIX),'v1_bug_scope':'Bool False is accepted by held v1 equality; demonstrated solely with fabricated records in isolated temporary roots. Corrected v2 rejects every non-int alias and conflicts.','original_plan_inverse':'Synthetic positive cases preserve every old semantic field/time and produce six exact original-byte aliases. These fixtures do not claim real owner integration or production execution.','protected_baseline':{'selection':ref('reports/full-coverage/checkpoint-24-selection.json'),'selected_proofs_rehashed':1144,'current_inventory':ref(inv)},'scope':'Independent code/read-only real-file check plus genuinely executed isolated synthetic fixtures only. No Root production plan closer, selector, integration, Lean, PUB or Git action was executed. Actual production closure records and successful prior interfaces/plan remain required.'}
REPORT.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'report':str(REPORT),'sha256':H(REPORT),'fixtures':len(FIX),'errors':[]}))
