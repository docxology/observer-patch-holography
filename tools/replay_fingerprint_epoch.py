#!/usr/bin/env python3
"""Replay four immutable fingerprint families at their real source epoch."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile

_spec = importlib.util.spec_from_file_location('oph_fingerprint_epoch_primitives', Path(__file__).with_name('replay_invariant_mining_epoch.py'))
assert _spec is not None and _spec.loader is not None
invariant = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(invariant)
HISTORICAL_EPOCH = 'bfa6c44d5347f113a5418d2a25d836f1057993a2'
CURRENT_EPOCH = invariant.LEAN435_EPOCH
PACKAGE = 'code/a5_fingerprint'
HISTORICAL_TESTS = frozenset(PACKAGE + '/' + name for name in [
    'test_seam_current_edge_prediction.py',
    'test_fz12_full_symbol_remainder_certificate.py',
    'test_fz12_free_photon_hamiltonian.py',
    'test_carrier_frequency_speed_certificate.py',
])
LEAN_NAMES = ('SeamCurrentCarrierQuotient', 'A5OrbitRaySeparation',
              'SeamCurrentEdge30Moment', 'SeamCurrentEdge30Remainder',
              'SeamCurrentFreePhotonLift', 'CarrierFrequencySpeed')
PROOF_API_ADAPTATIONS = frozenset({'Lean/Screen/CarrierFrequencySpeed.lean',
                                  'Lean/Screen/SeamCurrentCarrierQuotient.lean'})
REVIEWED_LEAN_DIFF_SHA256 = '339cee782ad5add59b3e31f89dbfa0fe2880555ec846eeced72639879258587f'


def validate(root: Path) -> dict[str, object]:
    root = root.resolve()
    require = invariant.require
    require(Path(invariant.git(root, 'rev-parse', '--show-toplevel').decode().strip()).resolve() == root,
            'repository root required')
    for epoch in (HISTORICAL_EPOCH, CURRENT_EPOCH):
        invariant.git(root, 'merge-base', '--is-ancestor', epoch, 'HEAD')
    tree = invariant.git(root, 'ls-tree', '-rz', HISTORICAL_EPOCH, '--', PACKAGE)
    rows: dict[str, bytes] = {}
    modes: dict[str, int] = {}
    for item in tree.rstrip(b'\0').split(b'\0'):
        metadata, name_raw = item.split(b'\t', 1)
        mode, kind, _ = metadata.split()
        require(kind == b'blob' and mode in {b'100644', b'100755'}, 'nonregular historical fingerprint source')
        name = invariant.relative(name_raw.decode())
        rows[name] = invariant.blob(root, HISTORICAL_EPOCH, name)
        modes[name] = int(mode, 8) & 0o777
    actual = set()
    for path in (root / PACKAGE).rglob('*'):
        if {'__pycache__', '.pytest_cache'} & set(path.relative_to(root / PACKAGE).parts):
            continue
        require(not path.is_symlink(), 'symbolic fingerprint entry refused')
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    require(actual == set(rows), 'historical fingerprint inventory changed')
    for name, payload in rows.items():
        require(invariant.live_bytes(root, name) == payload, 'historical fingerprint bytes changed: ' + name)
    pairs = []
    adapted = set()
    names = ['Lean/Screen/' + name + '.lean' for name in LEAN_NAMES]
    for name in names:
        historical = invariant.blob(root, HISTORICAL_EPOCH, name)
        current = invariant.live_bytes(root, name)
        require(current == invariant.blob(root, CURRENT_EPOCH, name), 'current fingerprint Lean source drift: ' + name)
        same_body = invariant.header_body(historical) == invariant.header_body(current)
        if not same_body:
            adapted.add(name)
        rows[name] = historical
        modes[name] = 0o644
        pairs.append({'path': name, 'historical_sha256': hashlib.sha256(historical).hexdigest(),
                      'current_sha256': hashlib.sha256(current).hexdigest(),
                      'imports_and_proof_body_identical': same_body})
    require(adapted == PROOF_API_ADAPTATIONS, 'reviewed proof API adaptation inventory changed')
    diff = invariant.git(root, 'diff', HISTORICAL_EPOCH, CURRENT_EPOCH, '--', *names)
    require(hashlib.sha256(diff).hexdigest() == REVIEWED_LEAN_DIFF_SHA256,
            'reviewed compiler migration diff changed')
    for name in ('Lean/lean-toolchain', 'Lean/lakefile.lean', 'Lean/lake-manifest.json'):
        require(invariant.live_bytes(root, name) == invariant.blob(root, CURRENT_EPOCH, name),
                'current fingerprint compiler/dependency context changed: ' + name)
    return {'root': root, 'files': rows, 'modes': modes, 'source_pairs': pairs,
            'historical_epoch': HISTORICAL_EPOCH, 'current_lean_epoch': CURRENT_EPOCH}


def replay(root: Path, tests: list[str] | None = None) -> None:
    selected = sorted(HISTORICAL_TESTS) if tests is None else tests
    invariant.require(bool(selected) and len(selected) == len(set(selected))
                      and set(selected) <= HISTORICAL_TESTS, 'unknown or duplicate historical fingerprint test')
    context = validate(root)
    with tempfile.TemporaryDirectory(prefix='oph-fingerprint-epoch-') as directory:
        capsule = invariant.materialize(context, Path(directory))
        print('Historical fingerprint families:', HISTORICAL_EPOCH, flush=True)
        subprocess.run([sys.executable, '-m', 'pytest', '-q', *selected], cwd=capsule, check=True)
        invariant.assert_capsule(context, capsule)
        validate(root)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        replay(args.repo_root)
    except invariant.EpochError as error:
        raise SystemExit(str(error)) from error

if __name__ == '__main__':
    main()
