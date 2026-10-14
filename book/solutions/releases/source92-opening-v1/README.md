# Source92 opening review and formal recovery

The interrupted pass is complete locally: **65 primer + 48 non-primer exercises**
reviewed, **56 replacements + 57 retained answers**. Primer0 is reviewed in full;
elsewhere the selection is the first three actual DOM exercises. All 556 questions,
hints and unselected solutions, authoring mirrors, anchors, scripts and all other
page bytes are preserved. [Plan](plan-v1.json) and [installation](installation-v1.json)
bind exact before/after identities and retain rationale for every selected answer.

The earlier Source91 release independently reviewed all 556 solutions. This
recovery separately reviews 23 module and 12 primer drafts saved before the crash.
The 21 additional recovery-authored replacements are explicitly self-reviewed;
no independent second-agent review is claimed for those new bodies. Retained and
unselected bodies keep their exact previous independent-review lineage.

[Reader QA](reader-QA-v1.json) passes every changed page at 320, 390, 768, 820 and
1280 pixels, including expanded disclosures, dynamic math, links, navigation,
print behavior and slider smoke checks. Four actual phone openings were inspected
at original resolution; this is not a claim to have visually inspected every
captured page. [Arithmetic](arithmetic-v1.json) recomputes worked values; finite
checks alone do not prove universal mathematical statements.

The Source92 selected audit is in
`../../../../reports/solution-review/runtime-source92-piece02-v1/reports/lean-verification/verification.json`.
It passes 1,272 files / 11,522 theorem axiom checks. Part(ii)'s 14 new bodies
received a fresh kernel replay in the original Source91 piece02 audit; the final
Source92 audit reuses only identical proof/import/dependency identities and runs
the aggregate build and every theorem axiom check again.

[Exact unchanged-source rebase](formal-rebase-v1.json) preserves part(i) and the
new part(ii) mapping: 27 mathematical clauses and 12 complete leaves. Exercise1.5
and all parent scopes remain partial; rounding/underflow and part(iii) are pending.
Opening rewrites receive zero automatic formal-completion credit.

Workspace installed-preservation reproduction:

```sh
python3 -B book/solutions/releases/source92-opening-v1/recover_release.py check --plan-sha256 101854993fd3cb88625c5bbe3ebe78f09b65fd41bc5c628451818ce235c3878b
```

For the exact frozen workspace Lean audit, run `verify.py` in
`reports/solution-review/runtime-source92-piece02-v1/verification/lean` with a
fresh output directory. In the published checkout the selected proofs are at
`verification/lean`; run `lake exe cache get` and `python3 verify.py --output
../../reports/source92-reproduction` there. Omitting reuse replays every module.
Actual commit/push/Pages/live hashes are recorded separately after delivery.
