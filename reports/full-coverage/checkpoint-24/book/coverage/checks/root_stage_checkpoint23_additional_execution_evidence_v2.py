"""TMP draft for Root-only supplemental23 publication evidence AFTER primary staging.
No execution or copy is performed by authoring this helper. The genuine failed
selector/binding executions remain failures; successful frozen audit is a mandatory
future prerequisite. All23 mathematical owner/source inputs are read-only.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess
ROOT = Path('/home/oxrexkevin/SafetyBased')
REPORTS = ROOT / 'reports/full-coverage'
PUBLICATION = ROOT / 'reports/book/publication-repo'
SNAPSHOT = REPORTS / 'checkpoint-23'
SELF_NAME = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v2.py'
ORIGINAL_UNEXECUTED_HELPER = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v1.py'
ORIGINAL_UNEXECUTED_HELPER_SHA = 'a78c008bf23113f484cd6c121d6c5e1c6807bed5f976f431a4852890b1ea7130'
PEER_NAME = 'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v1.json'
PRIMARY_HELPER = 'book/coverage/checks/root_prepare_and_stage_publication23_v3.py'
PRIMARY_HELPER_SHA = '9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb'
BASELINE_HELPER = 'book/coverage/checks/root_stage_checkpoint22_additional_execution_evidence_v1.py'
BASELINE_HELPER_SHA = 'fbde350b584b9204c0af797a95ee691c6ef51d8bec4cecf26b840d1ef089705f'
PINNED_CLOSED_EVIDENCE = {'reports/full-coverage/checkpoint23-root-independent-output-execution-v1.json': '91eede28c2861ffe3f5062fba1a1db95b83493dd3c9882054684fee5cc94b401', 'reports/full-coverage/checkpoint23-root-independent-output-execution-v1.log': 'b36a68e31de8e47f1d05f30719c1de57738aff489d6feb3dc8617b63c1459bae', 'reports/full-coverage/owner23-global-integrity-execution-v1.json': '87132378b7b2891f272410438bb2e05958fd8142188db97689367ed60038da0b', 'reports/full-coverage/owner23-global-integrity-execution-v1.log': '68e82e61797076c05de9d693281d630d870845f7ffe2003fff0f56d5640282a3', 'reports/full-coverage/static-checkpoint23-execution-v1.json': 'af4a095497994d357835a8d7df6cbac2e6510ad5742d9fa60454dc682c1329b6', 'reports/full-coverage/static-checkpoint23-execution-v1.log': '01e8629100d4554264498db109dd3bea31d3962810949e4cab886a6c00f42e28', 'reports/full-coverage/prepare-owner23-interface-request-execution-v1.json': '69722172d79b85f45a22949c90077416c03f84c6a6cf96cef9bdc066bc408cc4', 'reports/full-coverage/prepare-owner23-interface-request-execution-v1.log': '631da32491b89d9ef25f7f7f79d9869715ce5e79dc4a2500c6432586ceb6fe2e', 'reports/full-coverage/prepare-owner23-live-interfaces-execution-v1.json': '9bdca3d3bed078d560f20003f3f8b0a729806807f3e581b7dae4cc75afd15a6b', 'reports/full-coverage/prepare-owner23-live-interfaces-execution-v1.log': '517fdec8faa35158dd9d2cd7cddc2f2c71bd5d9fb95ae838e40f984b134115d7', 'reports/full-coverage/prepare-owner23-production-plan-execution-v1.json': 'f5a20d4c5d80ecb8adadf4d69bdb9d3c573b35147e0a90265c76443117a88f81', 'reports/full-coverage/prepare-owner23-production-plan-execution-v1.log': '352459d799d0c41f7d7a4107cc48d3342c5426934e7ac5c633384703060b39a1', 'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json': '001d9abb1c2b780a85866e56100d73f04c21090b3179132f9c7706080776b622', 'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.log': '7480b8bd08914cebd2ac82772e2a37dcd2cd76fd6a51a74eaa246adcc145f3dd', 'reports/full-coverage/prepare-checkpoint23-selection-execution-v2.json': '4a914e2542272279eff6c413144ad15d38001fe7422d38abeb9951a29cb0d394', 'reports/full-coverage/prepare-checkpoint23-selection-execution-v2.log': 'e78836b258a81eefc26522f7e97eeb0d4acaef7ffa5c867183e7ee5c5b349e91', 'reports/full-coverage/prepare-owner23-alias-plan-execution-v3.json': '83fd6ca17746e2afc09c43842db62008d2a80de7d32f1118f840f089f28d6264', 'reports/full-coverage/prepare-owner23-alias-plan-execution-v3.log': '132db9ab4dbcbaeaf9dd64e055f98b6001db8578e96083d9f64a12f7242d9823', 'reports/full-coverage/owner23-integration-apply-execution-v1.json': '4792b16b18e847313dc612a9c805ebbbbf48bbf335fa14c09f9333c38e77dde7', 'reports/full-coverage/owner23-integration-apply-execution-v1.log': '97ad9b5fe19030a4a6967fb126d28258873f2255526bb29096e9fc23b2f9ff15', 'reports/full-coverage/owner23-integration-dry-execution-v1.json': '359cf23bbc91da07a519a995abe1358c5689887e35d78d285c288a8d6d8a395c', 'reports/full-coverage/owner23-integration-dry-execution-v1.log': '73396cc5dea3a5c234d25cbdfe757e857017ebf307bb0ff9eec3a43e876cac28', 'reports/full-coverage/owner23-binding-preparation-execution-v1.json': '565462bd39c66aa17aa983d848672ac80725d02bc86ba2ccabfcea9d2fe0cd4b', 'reports/full-coverage/owner23-binding-preparation-execution-v1.log': '3b0b2a54d70278cd44478a1d2ffd48faf02c34c2dd21c5101f6cc15bc506bc54', 'reports/full-coverage/owner23-binding-preparation-execution-v2.json': '41cd13a26e05e8f3d62f6c625981b1ca6ddf880f9fb699cdd0762bfac64dd5ef', 'reports/full-coverage/owner23-binding-preparation-execution-v2.log': '917f53ea89c3aa3a41a4ada8c479d03f2fdda6346ca7eb33da86c88b2bff9c6d', 'reports/full-coverage/owner23-binding-preparation-execution-v3.json': '7a1fbfc0d57dc66c30ec5e1e4ceb83694d98dbf1b88ebd90bf55e8b224fb439b', 'reports/full-coverage/owner23-binding-preparation-execution-v3.log': 'bd5a3bd19288384fc0e64d1014226b8ab3af5625bc368dc1ff95743274c68d35', 'reports/full-coverage/core23-candidate-builder-execution-v1.json': '33012502a60eb0cdf44a69aa8dde5fdb262aaaab595027595adcab8ac5599f7d', 'reports/full-coverage/core23-candidate-builder-execution-v1.log': '7f344c48c3d3e336c1a8d606fd76a779f211b4612242ca574ab038c9147a49db', 'reports/full-coverage/core23-candidate-builder-execution-v2.json': '727faf53240aa468c69961783bacf9b393442691c358f693461745dd17f60f95', 'reports/full-coverage/core23-candidate-builder-execution-v2.log': 'ceef88c534136659dc8962a771a2cd201fa776169b5327e1810fc7bcab6f8515', 'reports/full-coverage/core23-candidate-offer-preparation-execution-v1.json': 'ce750d72a8c8d97465f86db0a0a59a9224f0cefef1ea1e0d09ca3be01aa33069', 'reports/full-coverage/core23-candidate-offer-preparation-execution-v1.log': '1c40316e8c5001ebe8cb33d24ca8a99dc2760108d007a080439a00accd97470e', 'reports/full-coverage/core23-final-reviewed-offer-execution-v1.json': '3696a4d79ad0587be54e554976926eef4d8fbc56de821d7216b9cb32ff142ab6', 'reports/full-coverage/core23-final-reviewed-offer-execution-v1.log': 'c2cdb540e86385190f96962f721541b22f289cd32f8181291fbbc01aa270bc45', 'reports/full-coverage/core23-nine-source-readiness-execution-v1.json': '8f82321f5be2a4d80e0d731de7a0c098e670e29c67d3b070b41b3b750765065a', 'reports/full-coverage/core23-nine-source-readiness-execution-v1.log': 'a50b7cc352532e7957e37a8ebcf2fc983b75d1e576095efcff8ca7e143a682ae', 'reports/full-coverage/browser-source51-23-runner-execution-v1.json': '4f8f74e712bcd95f33e5e5c6765b2cc558464d248a01824d02acc1b61b452f2c', 'reports/full-coverage/browser-source51-23-runner-execution-v1.log': '37d4da6e42be4ed93bc0ee9d4d2e6fbedd33c443b83823fc0e924bf16b6fe001', 'reports/full-coverage/browser-source51-23-v1-execution.json': 'a131ee9160861bde20a65e3806b418d394e821be58cb89ffbe26a5daa4aa4154', 'reports/full-coverage/browser-source51-23-v1-execution.log': '04c89088f8373bbd43458242d345756c89cc2468b32b93fe7beca8d2a44aaca9', 'reports/full-coverage/browser-checkpoint23-binding-execution-v1.json': '1dc4e4f1e3fef757c351501af98822e0ac0ebce5c8782216a8e582b053a4e184', 'reports/full-coverage/browser-checkpoint23-binding-execution-v1.log': '7e1773acf11dcaead6e5b5ef9a2e9866a9149a82c673c3920837967fbbc0e924', 'reports/full-coverage/root-monitoring23-canonical-pair-execution-v1.json': '915915355d0247959b0f97968e6bb863e52cc75f910ebd1df0ef3bfd18873203', 'reports/full-coverage/root-monitoring23-canonical-pair-execution-v1.log': 'bf260107f4ea7c6019ccc793be931ea04d2536279b012a836316c1bc0e632a0b', 'reports/full-coverage/root-monitoring-face23-canonical-pair-execution-v1.json': '7e0c529e6a61399b4af19e03efd7ae723ea6155b2fcd91ddf811421c6dd59360', 'reports/full-coverage/root-monitoring-face23-canonical-pair-execution-v1.log': '15e7fb9a488ba9c4afb49a6909afdb0070bfc70b613affa7efb8f2ed658cfce4', 'reports/full-coverage/root-monitoring-shift23-canonical-pair-execution-v1.json': '2b4b693be7d64304ae1544eae2cf7c888e88d2bbad161c0ad600fd26ca21f6f5', 'reports/full-coverage/root-monitoring-shift23-canonical-pair-execution-v1.log': '9116ec1cbae83ef3d005da5e54f3e8b84abfff7b8030b750b0d2411e1e187200', 'reports/full-coverage/root-monitoring-exposed23-canonical-pair-execution-v1.json': '92aa1db5b717428d1d668c16013f5aac01517994a19bb546cf7321248a6a3e8c', 'reports/full-coverage/root-monitoring-exposed23-canonical-pair-execution-v1.log': 'befe3db4cecb38f083d126ca133bec02a99ae468cd4dd0d0ff43928f816420ed', 'reports/full-coverage/source49-prewrite-execution-v1.json': '361c86bfa13caa04a982528537f1df83ba4e9f4be290fdcf882e70e1dacd8145', 'reports/full-coverage/source49-prewrite-execution-v1.log': '56d9b9a3de8b672472feef0381874bfeda883a90808f8d0a81767cc04458908c', 'reports/full-coverage/source49-apply-execution-v1.json': 'a224216735a16264f825d030dc97de36cfa9abbb215848ad743ed31935fe31dd', 'reports/full-coverage/source49-apply-execution-v1.log': '17b4bf4f554856729c689ef129434e6097391d2385f5e89710e8ecb650946bb9', 'reports/full-coverage/source50-prewrite-execution-v1.json': 'ed26cf158e7cf29a6a28c5d5b9593c1a54b96b38ded788ff1b7ffcc68ea37f8d', 'reports/full-coverage/source50-prewrite-execution-v1.log': '03f555087089fb4ee0b6632f639489fd012d5dacf16caf6bc3f57f931d3b70dc', 'reports/full-coverage/source50-apply-execution-v1.json': 'd80b3c24d8df07b30f0caea253b3671b63f926c53c7f39bc9182b31f69a64ed8', 'reports/full-coverage/source50-apply-execution-v1.log': '02847ee6e5cdadf0260951e7eb652a2ef0a5cf564b8bd9291ffa0e7d2e6b958c', 'reports/full-coverage/source51-prewrite-execution-v1.json': 'a23fd82653cb71ded93b976333024a87f92c6a1b1b30235a2613d91ac3693884', 'reports/full-coverage/source51-prewrite-execution-v1.log': '48cf51d4a64c2a5b1809dfc025cd853ab43c6f346b04cd3a1aba05062955848b', 'reports/full-coverage/source51-apply-execution-v1.json': '7a04def00fc4edbdd0459bc56d90e2cc056c08f6cda712e1f09fde75f4faea8f', 'reports/full-coverage/source51-apply-execution-v1.log': '3c190bcfd1ecb940da11e73eab3ad8300dae7f9190e199a65cd61e4164ba91c6', 'book/coverage/checks/future23-core/root-checkpoint23-production-output-independent-confirmation-v1.json': 'cac785822003b930ee6082ee73eaf21772637768a4d248a3cd0e4a2005e62eda', 'book/coverage/checks/future23-core/root-closed-report-original-byte-aliases23-v1.json': '84bad7614e8680c6e05657d709f3bec4a7615dffcfa4ae239257c655f7082268', 'book/coverage/checks/future23-core/root-selection-closed-original-byte-aliases23-v1.json': '17b4e7958e8691fa495eafb56b4ad716e830be52963a0d36ba471a71b5b063eb', 'reports/full-coverage/root-source51-final-owner-integration23-v1.json': '4c6358c1a58e35653efc064911240a9f1d3db8503cea12abe10a5fb6026c72b2', 'reports/full-coverage/owner23-reviewed-candidate-integration-v1.json': 'c9749696979b05e3207b014b0625b33155933bae14b0e5b548bb847416fb125b', 'reports/full-coverage/owner23-integration-guard-dry-run-v1.json': '6a90256c1d6dc3fda9a9a6b981a3cfdf938ca2372a383be5c0e1d889e9a8441f', 'reports/full-coverage/integration-23.json': '6a33b10e7775fd573ed6842a479c826745cc36b6d10aa608899d6b627c6e225b', 'reports/full-coverage/browser-source51-23-v1.json': 'b9af99359027cefa16fd9205f3254641ce3ff3be2cebf5a3918c60b8003d71a7', 'reports/full-coverage/browser-source51-23-v1-inputs.json': 'b714a4177d71a2fe728a23ac933ffbb95b081a923062667db530cac056b446f0', 'reports/full-coverage/browser-checkpoint-23.json': '5200f3f0b303891cf97d401f253c7bb50d1ba41f889abc3b6bafb9cc1f6afbc2', 'reports/full-coverage/browser-corrections-23-inputs.json': 'b5ed7f38a63e1363e2897bc6b57bdfc5c074b61cb8140bf857857e03ae583027', 'book/coverage/checks/root_check_export23_integrity_v1.py': '595b741f3b0189ff48f2fcf08374ad8bba66f9737d8bb51f5f184293d47834ef', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-independent-confirmation-v1.json': 'a0d104295bfbe48a611d2d9a5e0f89a514ceaf7c59e59a1a437174085c7c4301', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-peer-v1.py': '0b89a7d49c0df52bb3b4d3f59ea91c3f7df8fd7b83e4a229e48e8ea5ed9a4d5f', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-peer-actual-v1.json': '873e42c3732981096de0bac1e944ba3ec566a413acc364f9283e5d034d30663e', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-peer-actual-v1.log': '08edda4160a7ec6271b3a7da0a727703270fbcf9efdf03adb7613892dbf4615a', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-preserved-first-plan-checker-v1.py': 'b46f50c88d17f076468639634eae2b3c94e01a1124c0451e94353011403c5221', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-preserved-first-plan-actual-v1.json': '007cf2478be46d33c13e925230712bf6f573aaa5f592b3ec02db824b1e6441f0', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-preserved-first-plan-actual-v1.log': '9c319b24820d62ed19709f22332d9a0d1d6ea941f76f1ef4ce06d053fad75f9b', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-preserved-selector-failure-v1.json': '001d9abb1c2b780a85866e56100d73f04c21090b3179132f9c7706080776b622', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-preserved-selector-failure-v1.log': '7480b8bd08914cebd2ac82772e2a37dcd2cd76fd6a51a74eaa246adcc145f3dd', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-actual-alias-plan-v3.json': '83fd6ca17746e2afc09c43842db62008d2a80de7d32f1118f840f089f28d6264', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-actual-alias-plan-v3.log': '132db9ab4dbcbaeaf9dd64e055f98b6001db8578e96083d9f64a12f7242d9823', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-actual-selector-v2.json': '4a914e2542272279eff6c413144ad15d38001fe7422d38abeb9951a29cb0d394', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-actual-selector-v2.log': 'e78836b258a81eefc26522f7e97eeb0d4acaef7ffa5c867183e7ee5c5b349e91', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-selector-v1.py': '5811fc10687074862bfbb273017eb72c2f8990b4e44a18a4f2cf05c7037a8f67', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-retainer-v1.py': 'a6d122cfc0000360185acf9628693d4e041eefe0ed8b96e0f0bff5fb047859d1', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-selector-v2.py': '9fea9b7ad21f72079967a705f138b4451f55519b87b478df0a4cb1961f9c5a2e', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-retainer-v2.py': 'db95ec28d3d0a77d812e68cd1cc7bb1547a6d22e9f03f0672d76b20803ffb41a', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-plan-repair-v2.py': 'c84a2895470b6f98973d8d8972b9d1174f48d856baaa45c9880e327cc4b0622a', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-selector-v3.py': '3d646ccd946674944edd86bf55b10c5d5a4ee3cda4a1e7498f41aae8af6f226d', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-retainer-v3.py': '904341fa346e1e76cf6914b5660b978666bf0653664e75b1517e0400b9a25068', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-plan-repair-v3.py': 'd1688dbe882a4bb989f65293b8b7e232fcff106ba2afefcefb583c6eb2b1a243', 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-original-path-aliases-v1.json': 'daa5da24d4ac3793f454947b74ef3592af496c60fa5f2b838f0b6f1e8c749830'}
ORIGINAL_EXECUTION_CODES = {'checkpoint23-root-independent-output-execution-v1': 0, 'owner23-global-integrity-execution-v1': 0, 'static-checkpoint23-execution-v1': 0, 'prepare-owner23-interface-request-execution-v1': 0, 'prepare-owner23-live-interfaces-execution-v1': 0, 'prepare-owner23-production-plan-execution-v1': 0, 'prepare-checkpoint23-selection-execution-v1': 1, 'prepare-checkpoint23-selection-execution-v2': 0, 'prepare-owner23-alias-plan-execution-v3': 0, 'owner23-integration-apply-execution-v1': 0, 'owner23-integration-dry-execution-v1': 0, 'owner23-binding-preparation-execution-v1': 1, 'owner23-binding-preparation-execution-v2': 1, 'owner23-binding-preparation-execution-v3': 0, 'core23-candidate-builder-execution-v1': 0, 'core23-candidate-builder-execution-v2': 0, 'core23-candidate-offer-preparation-execution-v1': 0, 'core23-final-reviewed-offer-execution-v1': 0, 'core23-nine-source-readiness-execution-v1': 0, 'browser-source51-23-runner-execution-v1': 0, 'browser-source51-23-v1-execution': 0, 'browser-checkpoint23-binding-execution-v1': 0, 'root-monitoring23-canonical-pair-execution-v1': 0, 'root-monitoring-face23-canonical-pair-execution-v1': 0, 'root-monitoring-shift23-canonical-pair-execution-v1': 0, 'root-monitoring-exposed23-canonical-pair-execution-v1': 0, 'source49-prewrite-execution-v1': 0, 'source49-apply-execution-v1': 0, 'source50-prewrite-execution-v1': 0, 'source50-apply-execution-v1': 0, 'source51-prewrite-execution-v1': 0, 'source51-apply-execution-v1': 0}
SUCCESSFUL_LATER_EXECUTIONS = (
 'freeze-checkpoint23-execution-v1', 'cache-checkpoint23-execution-v1',
 'frozen-ledger-checkpoint23-execution-v1', 'verify-checkpoint23-execution-v1',
 'export-checkpoint23-execution-v1', 'prepare-publication23-execution-v1',
 'pages23-config-execution-v2', 'export-checkpoint23-output-integrity-execution-v1',
 'stage-publication23-execution-v1',
)
NATIVE_STAGE_NAMES = (
 'reports/full-coverage/publication-checkpoint23-staging-execution.json',
 'reports/full-coverage/publication-checkpoint23-staging-whitelist.json',
 'reports/full-coverage/publication-checkpoint23-stage-pathspec.nul',
 'reports/full-coverage/publication-checkpoint23-prestage-integrity.json',
 'reports/full-coverage/publication-extra23-files.json',
 'reports/full-coverage/lean-checkpoint-23/export-output-integrity-v1.json',
)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text())
def safe_name(name):
 assert isinstance(name,str) and name and not Path(name).is_absolute() and '..' not in Path(name).parts, name
 assert not any(c in name for c in ('\x00','\n','\r')), name
 return name

def source(name):
 path=ROOT/safe_name(name)
 assert path.is_file() and not path.is_symlink() and path.stat().st_size < 100_000_000, name
 return path

def execution(stem, expected_code):
 name='reports/full-coverage/'+stem+'.json'; row=read(source(name))
 codes=[row[k] for k in ('actual_exit_code','exit_code') if k in row]
 assert codes and all(type(c) is int and c==expected_code for c in codes),name
 assert isinstance(row['actual_command'],list) and row['actual_command'],name
 assert row['actual_workdir']==str(ROOT),name
 assert row['started_at_utc'] and row['finished_at_utc'] and row['elapsed_seconds']>=0,name
 assert sha(source(row['log']))==row['log_sha256'],name
 for key in ('helper_sha256_before','helper_sha256_after'):
  if key in row:
   assert all(sha(source(n))==d for n,d in row[key].items()),name
 if 'helper_sha256_before' in row and 'helper_sha256_after' in row:
  assert row['helper_sha256_before']==row['helper_sha256_after'],name
 return name,row

def dirty_names():
 names=set()
 for argv in (['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],
              ['git','ls-files','--others','--exclude-standard','-z']):
  names.update(x.decode() for x in subprocess.run(argv,cwd=PUBLICATION,capture_output=True,check=True).stdout.split(b'\0') if x)
 return names

assert Path(__file__).resolve()==ROOT/SELF_NAME
assert sha(source(PRIMARY_HELPER))==PRIMARY_HELPER_SHA
assert sha(source(BASELINE_HELPER))==BASELINE_HELPER_SHA
assert sha(source(ORIGINAL_UNEXECUTED_HELPER))==ORIGINAL_UNEXECUTED_HELPER_SHA
peer=read(source(PEER_NAME));assert 'passed' in peer['status'] and peer['errors']==[]
assert peer['helper_sha256']==sha(source(SELF_NAME))
manifest=read(source('reports/full-coverage/checkpoint-23-manifest.json'))
selection=read(source('reports/full-coverage/checkpoint-23-selection.json'))
audit=read(source('reports/full-coverage/lean-checkpoint-23/verification-original.json'))
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert sha(source('reports/full-coverage/checkpoint-23-selection.json'))==manifest['selection_sha256']
assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1131
assert audit['status']=='passed' and audit['theorem_count']==9193
assert all(row['exit_code']==0 for row in audit['checks'])
for name,row in manifest['proof_files'].items():
 assert sha(ROOT/safe_name(name))==sha(SNAPSHOT/name)==row['sha256'],name
for name,digest in manifest['frozen_inputs_sha256'].items():
 assert sha(SNAPSHOT/safe_name(name))==digest,name
assert sha(SNAPSHOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
for owner in ('core','modules','foundations','applied'):
 name='book/coverage/'+owner+'.json';assert sha(source(name))==manifest['working_inputs_sha256'][name],name
assert sha(source('book/coverage/applied-promotions.json'))==manifest['working_inputs_sha256']['book/coverage/applied-promotions.json']
# Pruned publication Applied metadata has already been checked by immutable primary staging.
primary_native=read(source(NATIVE_STAGE_NAMES[0]));assert primary_native['status']=='passed_explicit_whitelist_staged'
assert primary_native['actual_exit_code']==0
base_list=read(source(NATIVE_STAGE_NAMES[1]));assert len(base_list)==len(set(base_list))
base={safe_name(n) for n in base_list}
assert source(NATIVE_STAGE_NAMES[2]).read_bytes()==b''.join(n.encode()+b'\0' for n in sorted(base))
primary_integrity=read(source(NATIVE_STAGE_NAMES[3]));assert primary_integrity['status']=='passed_exact_frozen_and_explicit_actual_evidence'
assert primary_native['integrity_record']==NATIVE_STAGE_NAMES[3] and primary_native['integrity_record_sha256']==sha(source(NATIVE_STAGE_NAMES[3]))
for name,digest in primary_integrity['paths_sha256'].items():
 assert sha(PUBLICATION/safe_name(name))==digest,name
for name,digest in PINNED_CLOSED_EVIDENCE.items():assert sha(source(name))==digest,name
names=set(PINNED_CLOSED_EVIDENCE)|set(NATIVE_STAGE_NAMES)|{SELF_NAME,PEER_NAME,ORIGINAL_UNEXECUTED_HELPER}
records={}
for stem,expected_code in list(ORIGINAL_EXECUTION_CODES.items())+[(n,0) for n in SUCCESSFUL_LATER_EXECUTIONS]:
 name,row=execution(stem,expected_code);names.update((name,row['log']));records[name]={'sha256':sha(source(name)),'actual_exit_code':expected_code,'log_sha256':row['log_sha256']}
assert read(source('reports/full-coverage/stage-publication23-execution-v1.json'))['actual_command']==['python3',PRIMARY_HELPER]
export_integrity=read(source(NATIVE_STAGE_NAMES[-1]));assert export_integrity['status']=='passed'
assert (export_integrity['fresh_kernel_replays'],export_integrity['exact_original_kernel_replays_reused'])==(18,1113)
assert 'verification/lean/' not in '\n'.join(names)
# Validate every proposed copy and every existing target before any mutation.
expected={name:sha(source(name)) for name in sorted(names)}
for name,digest in expected.items():
 target=PUBLICATION/name
 if target.exists():assert target.is_file() and not target.is_symlink() and sha(target)==digest,name
assert dirty_names()<=base|names
out=REPORTS/'publication-checkpoint23-additional-execution-evidence-v1.json'
pathspec=REPORTS/'publication-checkpoint23-additional-evidence-pathspec-v1.nul'
assert not out.exists() and not pathspec.exists()
for name,digest in expected.items():
 target=PUBLICATION/name;target.parent.mkdir(parents=True,exist_ok=True)
 if not target.exists():shutil.copyfile(source(name),target)
 assert sha(source(name))==sha(target)==digest,name
assert dirty_names()<=base|names
pathspec.write_bytes(b''.join(name.encode()+b'\0' for name in sorted(names)))
cmd=['git','add','-f','--pathspec-from-file='+str(pathspec),'--pathspec-file-nul']
res=subprocess.run(cmd,cwd=PUBLICATION,capture_output=True)
assert res.returncode==0,(res.stdout,res.stderr)
staged=subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUBLICATION,capture_output=True,check=True).stdout
assert {x.decode() for x in staged.split(b'\0') if x}<=base|names
out.write_text(json.dumps({'status':'passed_exact_additional_actual_execution_evidence_explicitly_staged',
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),'paths_sha256':expected,
 'actual_execution_records':records,'actual_git_command':cmd,'actual_git_workdir':str(PUBLICATION),
 'actual_git_exit_code':res.returncode,'primary_stage_helper_sha256':PRIMARY_HELPER_SHA,
 'scope':'Exact closed original execution histories; actual failed records retained as failures. No mathematical owner/source edit, proof selection, compiler execution, new coverage or prior provenance relabeling.',
 'coverage_complete':False},indent=2)+'\n')
print(json.dumps({'status':'passed','additional_evidence_paths':len(names)}))
