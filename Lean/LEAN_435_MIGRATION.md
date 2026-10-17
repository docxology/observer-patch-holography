# Lean 4.35 compatibility

Both Lake packages use `leanprover/lean4:v4.35.0` and Mathlib release
`v4.35.0`, resolved to `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Their manifests contain portable Git dependencies.

The migration was checked against baseline commit
`bfa6c44d5347f113a5418d2a25d836f1057993a2` with the compatibility patch
applied. The root default targets passed 9,624 Lake jobs, NormalForms passed
9,064, and the optional OphGap certificate passed 9,069. These are Lake
job counts, including dependency jobs, rather than theorem counts.

Reproduce the strict builds from the repository root:

```sh
(cd Lean && lake --wfail build)
(cd Lean/ObservableNormalForms && lake --wfail build)
(cd Lean && lake --wfail build OphGap)
```

The proofs retain their statements and hypotheses. Compatibility repairs use
explicit algebra homomorphisms, pointwise derivative APIs, transparent data
aliases, and bounded finite checks. Proof budgets were not increased.
The native-decision inventory still permits only the existing thirteen
reviewed sites. Negative axiom-audit controls reuse an existing reviewed
proof instead of creating new compiler-trusted oracles. The inventory now
lexes comments and literals and detects inline tactic calls.

The tooling suite passed 601 tests with two skips using the pinned
`requirements.txt` environment. This qualifies `tools/`; it does not claim
that every optional scientific or hardware lane was executed. Reproduce it
with `.venv/bin/python -m pytest -q tools`. The docstring, theorem-count,
CI-budget, and native-decision inventory checks also pass.

Historical receipts and frozen evidence retain their original hashes. They
are not rewritten as receipts for this migration. For the generated OphGap
modules, only the module preamble changes; certificate declarations remain
byte-identical. See `OphGap/README.md` for generator ownership.
