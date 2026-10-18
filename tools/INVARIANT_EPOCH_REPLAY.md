# Archival replay of the sealed invariant-mining campaign

`replay_invariant_mining_epoch.py` replays the unchanged campaign at its actual
historical Git commit, `e602f4b71b67cd1e26b245ed7a2a8f9d48b9b683`.
It does not replace the independent verifier or establish a new campaign.

The original live verifier refuses the current source tree because nine pinned
Lean files changed during the Lean 4.35 migration. Their imports and complete
proof bodies are identical after removing the reviewed module/public-import
headers. The archival tool requires the exact historical blobs and the exact
current blobs from `a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2`, both in real
ancestor history. It also checks the entire frozen package inventory, all 41
source/control pins and the current compiler/dependency context.

From the repository root, with the documented Python dependencies installed:

```sh
python tools/replay_invariant_mining_epoch.py --mode verify
python tools/replay_invariant_mining_epoch.py --mode tests
python tools/replay_invariant_mining_epoch.py --mode builders
python -m pytest -q code/audit/test_invariant_epoch_replay.py
```

Each replay materializes actual historical Git blobs in a temporary directory
outside the live repository, runs the original commands unchanged and checks
the source bytes afterward. The builder mode uses `--check` exclusively.
The test mode runs the original campaign mutation tests. The live campaign,
candidate registry, generation policy and comparison seal remain unchanged.
New source drift, a coherent reseal, added campaign payloads, missing history,
unrelated history and altered capsules are refused.

Passing archival replay establishes reproducibility of the historical campaign.
It does not authorize live generation against drifted sources, unseal comparison
data, prove new physical predictions or constitute a complete current mandatory
suite run. Selecting a current CI compatibility context remains a separate
review decision.
