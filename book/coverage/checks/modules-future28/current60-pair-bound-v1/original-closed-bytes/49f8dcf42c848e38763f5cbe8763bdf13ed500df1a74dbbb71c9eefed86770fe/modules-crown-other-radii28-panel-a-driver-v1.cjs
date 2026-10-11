const fs = require('fs');
const vm = require('vm');
const crypto = require('crypto');
const assert = require('assert');
const source = '/home/oxrexkevin/SafetyBased/SafeLearning/verification.html';
const original = fs.readFileSync(source, 'utf8');
const digest = x => crypto.createHash('sha256').update(x).digest('hex');
assert.equal(digest(Buffer.from(original)), 'd01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53');
const start = original.indexOf('// ===== Panel A: output bounds of the 2-2-1 ReLU network =====');
const end = original.indexOf('// ===== Panel B: split conformal coverage versus calibration size =====', start);
assert(start > 0 && end > start);
const script = original.slice(start, end);
const results = [];
for (const eps of [0.5, 1.5]) {
  const values = {w11: 1, w12: 1, w21: -1, w22: 2, b1: 1, b2: 1, v1: -2, v2: 2, eps};
  const elements = new Map();
  const document = {getElementById(id) {
    if (!elements.has(id)) elements.set(id, {
      value: id === 'vfa-slice' ? 'diag' : String(values[id.replace(/^vfa-/, '')] ?? ''),
      innerHTML: '', textContent: '', addEventListener() {}
    });
    return elements.get(id);
  }};
  vm.runInNewContext(script, {document, Math}, {timeout: 10000});
  const info = elements.get('vfa-info').innerHTML;
  const expected = eps === 0.5 ? [
    'z<sub>1</sub> ∈ [2.00, 4.00] <em>active</em>',
    'z<sub>2</sub> ∈ [0.50, 3.50] <em>active</em>',
    'IBP [−7.00, 3.00]', 'CROWN (adaptive α = 1,1) [−5.00, 1.00]',
    'α-CROWN [−5.00, 1.00]', 'exact [−5.00, 1.00]'
  ] : [
    'z<sub>1</sub> ∈ [0.00, 6.00] <em>active</em>',
    'z<sub>2</sub> ∈ [−2.50, 6.50] <em>unstable</em>',
    'IBP [−12.00, 13.00]', 'CROWN (adaptive α = 1,1) [−11.00, 7.00]',
    'α-CROWN [−8.50, 7.00]', 'α<sub>2</sub> = 0.50', 'exact [−8.50, 7.00]'
  ];
  for (const text of expected) assert(info.includes(text), `epsilon ${eps} missing ${text}`);
  assert(elements.get('vfa-svg').innerHTML.includes('<polyline'));
  assert(elements.get('vfa-box').innerHTML.includes('<polygon'));
  results.push({epsilon: eps, full_native_panel_a_info_html: info, expected_checked_strings: expected,
    produced_plot_svg: true, produced_input_box_svg: true});
}
assert.equal(digest(fs.readFileSync(source)), digest(Buffer.from(original)));
console.log(JSON.stringify({status: 'passed_actual_current55_panel_a_runtime_at_two_requested_radii',
  source, source_sha256: digest(Buffer.from(original)), extracted_unmodified_panel_a_script_sha256: digest(Buffer.from(script)),
  extracted_unmodified_panel_a_script_bytes: Buffer.byteLength(script), results,
  source_unchanged: true, instrumentation: 'Actual complete unmodified Panel A IIFE evaluated with document element stubs; checks use its displayed numerical results.'}));
