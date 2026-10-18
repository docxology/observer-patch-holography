# Current mandatory compatibility profile

Use `python tools/run_current_mandatory_suite.py --full --certificates` for the
current profile. The original byte-frozen `run_mandatory_suite.py` still owns
all CLI flags, full/certificate selection, heavy-step policy and sharding.
Its file and the sealed campaign are unchanged.

Two source contexts require explicit archival replay after Lean 4.35:

| Checks | Actual Git source context |
|---|---|
| Original invariant-mining verifier and all original mutation tests | `e602f4b71b67cd1e26b245ed7a2a8f9d48b9b683` |
| Four fingerprint families: seam edge, full-symbol remainder, free-photon lift and carrier frequency | `bfa6c44d5347f113a5418d2a25d836f1057993a2` |
| Every other original check, including the other 15 fingerprint test files and exact certificate suites | Current worktree |

The four historical fingerprint files are executed in their original order,
interleaved with the current files using separate processes for contiguous
source contexts. This avoids Python module-cache mixing. All 19 original
fingerprint files run exactly once; no assertion, case or file is deselected.
The two original invariant commands keep their original argv and run inside
their historical capsule. Every other command and working directory stays
current. A full profile retains all 162 original owner steps; separating the
fingerprint contexts adds eight child invocations.

Before dispatch, the tools require real ancestor history, exact historical Git
blobs, complete unchanged frozen package inventories, all 41 invariant pins,
and exact current Lean/compiler/dependency bytes from the reviewed migration
commit `a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2`.
The nine invariant Lean files changed only module/public-import headers.
Four of the six fingerprint counterparts also have identical proof bodies;
the other two contain reviewed Mathlib API/tactic adaptations with unchanged
theorem statements. The exact six-file Git diff is pinned, rather than allowing
arbitrary proof edits under a migration label.

Capsules are built outside the live repository from actual Git blobs. Original
verifiers, builders, mutation tests and receipts remain unchanged. Capsule and
live source checks run again after execution. Unexpected files, coherent
resealing, altered current proofs and objects without actual ancestry fail
closed. Full history is required on every mandatory CI worker.

The current Lean counterparts were compiled strictly with Lean 4.35; the
existing Lean CI continues to compile the current library separately. Archival
Python replay does not substitute for native Lean verification. A passing
compatibility profile establishes this explicitly mixed source-context replay.
It does not mean the original live-source freeze accepts the migrated tree,
authorize generation against new source bytes, unseal comparison data, or
establish missing physical predictions.

Standalone archival checks:

```sh
python tools/replay_invariant_mining_epoch.py --mode verify
python tools/replay_invariant_mining_epoch.py --mode tests
python tools/replay_fingerprint_epoch.py
python -m pytest -q tools/test_current_mandatory_context.py \
  code/audit/test_invariant_epoch_replay.py \
  code/audit/test_fingerprint_epoch_replay.py
```
