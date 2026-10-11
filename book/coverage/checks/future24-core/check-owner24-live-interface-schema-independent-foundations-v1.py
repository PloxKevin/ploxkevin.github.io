from pathlib import Path
import json,copy,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=ROOT/'book/coverage/prepare_checkpoint24_live_owner_interfaces_v1.py'
assert hashlib.sha256(HELPER.read_bytes()).hexdigest()=='a48d00b6fc41774f5aa2da37f697ded86b3af78fd245b9c675d7897fb0b67ba1'
ns={'__name__':'independent_schema_fixture','__file__':str(HELPER)}
exec(compile(HELPER.read_text(),str(HELPER),'exec'),ns)
# Isolated read-only fixture: this is a real original offer and an in-memory
# reproduction of the helper's additions collision; no interface/main execution.
p=ROOT/'book/coverage/checks/applied-future24/source52/applied-audit24-candidate-source52-additions-v1.json'
o=json.loads(p.read_text())
assert isinstance(o['required_live_integration_evidence_sha256'],dict)
assert o['required_live_integration_evidence_sha256']
additions={'required_live_integration_evidence_sha256':{}}
assert not (set(additions)&set(o)), 'Actual Applied52 original already has required_live_integration_evidence_sha256: v1 additions collision rejects the valid original offer; NEW reversible merge needed.'
