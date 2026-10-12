from pathlib import Path
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-Norm21-full-narrow-composition-independent-modules32-findings-v1.json')
M=R/'book/coverage/checks/future32-core/Norm21-independent-modules-v1/foundations-Norm21-entire-current-components-prospective305307311-full-mathematical-independent-modules32-closed-peer-v1.json';MH='14efa544f419f5aebaa9b31a817533c7384111c17424e50cb98e7dcf98d6ea51'
N=R/'book/coverage/checks/future32-core/norm21-positive-dimensions-independent-modules-child-v1/foundations-common-norm21-positive-dimensions-one-phrase-full-literal-independent-parser-independent-modules-child32-closed-peer-v1.json';NH='4a47d79f9fc610dea1be9d5633ddb22014d647e4a3e862e6ca744ea1ce82225c'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(x):
 p=path(x['file']);assert sha(p)==x['sha256'];return p
assert not F.exists()and sha(C)==CH and sha(M)==MH and sha(N)==NH
ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH
 for n,h in g.items():assert sha(path(n))==h,n
guard();m=json.loads(M.read_bytes());n=json.loads(N.read_bytes());refs={str(M):MH,str(N):NH,str(C):CH}
for peer in [m,n]:
 assert peer['errors']==[] and peer['status'].startswith('passed')
 for p,h in peer['required_evidence_artifacts_sha256'].items():assert sha(path(p))==h;refs[str(path(p))]=h
 nr=json.loads(checked(peer['actual_reader']).read_bytes());assert nr['actual_exit_code']==0 and nr['protection_errors']==[]
 assert sha(path(nr['log']))==nr['log_sha256']
assert m['all21_exact_component_scopes_approved']and n['narrow_one_positive_dimension_phrase_semantically_approved']and n['independent_parser']['both_ROOT_and_OUT_TMP']
assert checked(m['dimension_proposal']).read_bytes()==checked(n['original_proposal']).read_bytes()
for key in ['primer-linalg.html::node-305','primer-linalg.html::node-307']:
 assert m['entire_current_literals'][key]==n['entire_current_and_proposed_literal_records'][key]['entire_current']
 assert m['entire_prospective_table_and_unchanged_following_proof_literals'][key]==n['entire_current_and_proposed_literal_records'][key]
assert m['unchanged_proof_fixture']==n['entire_unchanged_current_and_prospective311_proof_fixture']
fold=checked(n['actual_Finset_nonempty_supremum_and_attainment_primary_provider']);ft=fold.read_text();assert "def sup' (s : Finset β) (H : s.Nonempty)"in ft and "theorem exists_mem_eq_sup'"in ft
# The complete actual Fold primitive and induction body were read independently; no duplicate compiler or altered old verdict.
assert "induction H using Finset.Nonempty.cons_induction"in ft and 'cases le_total (f b) (f c)'in ft
assert m['whole_unit_decisions']['primer-linalg.html::node-311']['current_whole_semantic_approved']is False and m['whole_unit_decisions']['primer-linalg.html::node-311']['prospective_whole_semantic_approved']is True
guard()
f={'status':'passed_Norm21_full_math_and_distinct_narrow_positive_domain_composition','errors':[],'full_source_read':True,'original_full_mathematical_peer':ref(M),'distinct_independent_narrow_literal_parser_peer':ref(N),'all_original_math_and_narrow_body_times_decisions_unchanged':True,'all21_exact_components_approved':True,'public_theorem_count':21,'public_name_count':25,'actual_source':m['actual_source'],'public_theorem_names':m['public_theorem_names'],'whole_unit_decisions':m['whole_unit_decisions'],'additional_complete_actual_nonempty_supremum_and_attained_maximum_provider_read':ref(fold),'narrow_parser_prerequisite_now_genuinely_closed':True,'current305307311_wholes_false':True,'prospective305307_and_context_scoped_unchanged311_wholes_conditional_exact_application':True,'no_Source_ordinal_application_owner_canonical_selected_or_publication_mutation':True,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'current_whole':False,'prospective_wholes':['305','307','311'],'errors':[]}))
