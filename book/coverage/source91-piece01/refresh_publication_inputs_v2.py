"""Create fresh piece01 publication inputs after the preserved writer refusal."""
import common as c
import prepare_publication_inputs as inputs

review = c.read('reports/full-coverage/source91-piece01/publication-inputs-independent-review-v2.json')
assert review['status'] == 'approved' and not review['errors']
for binding in review['reviewed_helpers']:
    c.exact(binding)
inputs.LIST = 'reports/full-coverage/source91-piece01/publication-files-v2.json'
inputs.REPORT = 'reports/full-coverage/source91-piece01/publication-inputs-v2.json'
inputs.main()
