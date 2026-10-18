#!/usr/bin/env python3
"""Replay the unchanged sealed campaign at its real historical source epoch.

This is an archival orchestrator, not a replacement independent verifier.
The live verifier remains fail-closed on source drift. No freeze is rebuilt.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile

HISTORICAL_EPOCH = 'e602f4b71b67cd1e26b245ed7a2a8f9d48b9b683'
LEAN435_EPOCH = 'a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2'
PACKAGE = 'code/invariant_mining'
LEAN_PAIRS = frozenset({
    'Lean/ObserverPatchHolography/CapacityNonidentifiability.lean',
    'Lean/ObserverPatchHolography/CoreAxioms.lean',
    'Lean/Screen/A5FamilyBand.lean',
    'Lean/Screen/A5IncidenceResponse.lean',
    'Lean/Screen/A5PortAction.lean',
    'Lean/Screen/A5PortModule.lean',
    'Lean/Screen/EqualStateWeights.lean',
    'Lean/Screen/KineticFamilyCancellation.lean',
    'Lean/Screen/Z6Exact.lean',
})

class EpochError(ValueError):
    """A purported archival context is not the reviewed source transition."""

def require(condition: bool, detail: str) -> None:
    if not condition:
        raise EpochError(detail)

def git(root: Path, *args: str) -> bytes:
    result = subprocess.run(['git', '-C', str(root), *args], capture_output=True)
    require(result.returncode == 0, 'required local Git history unavailable: ' + ' '.join(args))
    return result.stdout

def relative(value: str) -> str:
    path = PurePosixPath(value)
    require(bool(value) and not path.is_absolute() and '..' not in path.parts
            and '\\' not in value and '\x00' not in value,
            'noncanonical source path')
    return value

def blob(root: Path, epoch: str, name: str) -> bytes:
    return git(root, 'show', epoch + ':' + relative(name))

def live_bytes(root: Path, name: str) -> bytes:
    path = root / relative(name)
    require(not any(p.is_symlink() for p in [path, *path.parents] if p != root.parent),
            'symbolic source path refused: ' + name)
    require(path.is_file(), 'source file missing: ' + name)
    return path.read_bytes()

def header_body(payload: bytes) -> tuple[list[str], str]:
    lines = payload.decode('utf-8').splitlines(keepends=True)
    imports: list[str] = []
    index = 0
    for index, line in enumerate(lines):
        if line.strip() in {'', 'module', '@[expose] public section'}:
            continue
        if line.startswith(('import ', 'public import ')):
            imports.append(line.removeprefix('public '))
            continue
        break
    return imports, ''.join(lines[index:])

def validate(root: Path) -> dict[str, object]:
    root = root.resolve()
    top = Path(git(root, 'rev-parse', '--show-toplevel').decode().strip()).resolve()
    require(top == root, 'repository root required')
    for epoch in [HISTORICAL_EPOCH, LEAN435_EPOCH]:
        git(root, 'merge-base', '--is-ancestor', epoch, 'HEAD')
    projection_name = PACKAGE + '/outputs/source_projection.json'
    projection_bytes = blob(root, HISTORICAL_EPOCH, projection_name)
    require(live_bytes(root, projection_name) == projection_bytes, 'frozen projection changed')
    projection = json.loads(projection_bytes)
    pins = projection['control_documents'] + projection['source_artifacts']
    require(len(pins) == 41, 'historical pin census changed')
    rows: dict[str, bytes] = {}
    modes: dict[str, int] = {}
    tree = git(root, 'ls-tree', '-rz', HISTORICAL_EPOCH, '--', PACKAGE)
    for item in tree.rstrip(b'\x00').split(b'\x00'):
        metadata, raw_name = item.split(b'\t', 1)
        mode, kind, _ = metadata.split()
        require(kind == b'blob' and mode in {b'100644', b'100755'}, 'nonregular historical source')
        name = relative(raw_name.decode('utf-8'))
        rows[name] = blob(root, HISTORICAL_EPOCH, name)
        modes[name] = int(mode, 8) & 0o777
    expected_package = set(rows)
    actual_package = set()
    for path in (root / PACKAGE).rglob('*'):
        if {'__pycache__', '.pytest_cache'} & set(path.relative_to(root / PACKAGE).parts):
            continue
        require(not path.is_symlink(), 'symbolic campaign entry refused')
        if path.is_file():
            actual_package.add(path.relative_to(root).as_posix())
    require(actual_package == expected_package, 'frozen campaign inventory changed')
    for name, payload in rows.items():
        require(live_bytes(root, name) == payload, 'frozen campaign bytes changed: ' + name)
    changed = set()
    pairs = []
    for pin in pins:
        name = relative(pin['path'])
        historical = blob(root, HISTORICAL_EPOCH, name)
        require(len(historical) == pin['bytes']
                and 'sha256:' + hashlib.sha256(historical).hexdigest() == pin['sha256'],
                'historical pin does not bind its Git blob: ' + name)
        current = live_bytes(root, name)
        if current != historical:
            require(name in LEAN_PAIRS, 'unreviewed source drift: ' + name)
            require(current == blob(root, LEAN435_EPOCH, name), 'current Lean source drift: ' + name)
            require(header_body(historical) == header_body(current), 'proof body or imports changed: ' + name)
            changed.add(name)
            pairs.append({'path': name, 'historical_sha256': hashlib.sha256(historical).hexdigest(),
                          'current_sha256': hashlib.sha256(current).hexdigest()})
        rows[name] = historical
        modes.setdefault(name, 0o644)
    require(changed == LEAN_PAIRS, 'reviewed Lean source transition is incomplete')
    for name in ['Lean/lean-toolchain', 'Lean/lakefile.lean', 'Lean/lake-manifest.json']:
        require(live_bytes(root, name) == blob(root, LEAN435_EPOCH, name),
                'current compiler/dependency context changed: ' + name)
    return {'root': root, 'files': rows, 'modes': modes, 'source_pairs': pairs,
            'historical_epoch': HISTORICAL_EPOCH, 'current_lean_epoch': LEAN435_EPOCH}

def materialize(context: dict[str, object], destination: Path) -> Path:
    root = context['root']
    assert isinstance(root, Path)
    destination = destination.resolve()
    require(destination != root and root not in destination.parents,
            'archival capsule must be outside the live repository')
    require(not destination.exists() or not any(destination.iterdir()), 'capsule destination is not empty')
    destination.mkdir(parents=True, exist_ok=True)
    files = context['files']
    modes = context['modes']
    assert isinstance(files, dict) and isinstance(modes, dict)
    for name, payload in files.items():
        path = destination / relative(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)
        path.chmod(modes[name])
    return destination

def assert_capsule(context: dict[str, object], capsule: Path) -> None:
    files = context['files']
    assert isinstance(files, dict)
    actual = set()
    for path in capsule.rglob('*'):
        if {'__pycache__', '.pytest_cache'} & set(path.relative_to(capsule).parts):
            continue
        require(not path.is_symlink(), 'symbolic historical capsule entry refused')
        if path.is_file():
            actual.add(path.relative_to(capsule).as_posix())
    require(actual == set(files), 'historical capsule inventory changed')
    for name, payload in files.items():
        require(live_bytes(capsule, name) == payload, 'historical capsule changed: ' + name)

def commands(mode: str) -> list[list[str]]:
    if mode == 'verify':
        return [[sys.executable, PACKAGE + '/tools/verify_pregeneration_freeze_independent.py']]
    if mode == 'tests':
        return [[sys.executable, '-m', 'pytest', '-q', PACKAGE + '/tests/test_pregeneration_lock.py']]
    require(mode == 'builders', 'unknown archival replay mode')
    return [[sys.executable, PACKAGE + '/tools/' + name + '.py', '--check']
            for name in ['build_source_projection', 'build_pregeneration_freeze', 'generate_candidates']]

def replay(root: Path, mode: str) -> None:
    context = validate(root)
    with tempfile.TemporaryDirectory(prefix='oph-invariant-epoch-') as directory:
        capsule = materialize(context, Path(directory))
        print('Historical sealed invariant campaign:', HISTORICAL_EPOCH, flush=True)
        print('Current Lean counterparts recognized; live source-drift refusal is unchanged.', flush=True)
        for command in commands(mode):
            subprocess.run(command, cwd=capsule, check=True)
            assert_capsule(context, capsule)
        validate(root)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--mode', choices=['verify', 'tests', 'builders'], default='verify')
    args = parser.parse_args()
    try:
        replay(args.repo_root, args.mode)
    except EpochError as error:
        raise SystemExit(str(error)) from error

if __name__ == '__main__':
    main()
