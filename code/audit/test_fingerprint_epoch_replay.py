"""Real Git and real original-test controls for historical fingerprint replay."""
from pathlib import Path
import importlib.util
import json
import subprocess
import sys
import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('oph_fingerprint_replay_audit', ROOT / 'tools/replay_fingerprint_epoch.py')
assert spec is not None and spec.loader is not None
epoch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(epoch)

@pytest.fixture(scope='module')
def source_context():
    return epoch.validate(ROOT)

@pytest.fixture
def live(tmp_path, source_context):
    root = tmp_path / 'live'
    subprocess.run(['git', 'clone', '--shared', '--no-checkout', str(ROOT), str(root)], check=True, capture_output=True)
    for name in [*source_context['files'], 'Lean/lean-toolchain', 'Lean/lakefile.lean', 'Lean/lake-manifest.json']:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes((ROOT / name).read_bytes())
    return root


def test_all_four_original_families_replay_in_actual_historical_context(live, tmp_path):
    context = epoch.validate(live)
    capsule = epoch.invariant.materialize(context, tmp_path / 'historical')
    result = subprocess.run([sys.executable, '-m', 'pytest', '-q', *sorted(epoch.HISTORICAL_TESTS)],
                            cwd=capsule, capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    epoch.invariant.assert_capsule(context, capsule)
    assert sum(not p['imports_and_proof_body_identical'] for p in context['source_pairs']) == 2


@pytest.mark.parametrize('name', epoch.LEAN_NAMES)
def test_current_proof_tampering_is_not_an_epoch_exception(live, name):
    path = live / ('Lean/Screen/' + name + '.lean')
    path.write_bytes(path.read_bytes() + b'\n-- unreviewed current change\n')
    with pytest.raises(ValueError, match='current fingerprint Lean source drift'):
        epoch.validate(live)


def test_coherently_resigned_receipt_is_still_not_the_historical_receipt(live):
    path = live / 'code/a5_fingerprint/runtime/seam_current_edge_prediction_receipt.json'
    payload = json.loads(path.read_bytes())
    payload['status'] = 'UNREVIEWED_PROMOTION'
    payload.pop('receipt_sha256')
    import hashlib
    canonical = lambda value: (json.dumps(value, allow_nan=False, ensure_ascii=True,
                                        separators=(',', ':'), sort_keys=True) + '\n').encode('ascii')
    payload['receipt_sha256'] = 'sha256:' + hashlib.sha256(canonical(payload)).hexdigest()
    path.write_bytes(canonical(payload))
    with pytest.raises(ValueError, match='historical fingerprint bytes changed'):
        epoch.validate(live)


def test_new_comparison_payload_is_refused(live):
    (live / 'code/a5_fingerprint/runtime/new_target.csv').write_text('target,value\nx,1\n')
    with pytest.raises(ValueError, match='historical fingerprint inventory changed'):
        epoch.validate(live)


def test_historical_objects_without_actual_ancestry_are_refused(live):
    subprocess.run(['git', 'config', 'user.name', 'Epoch fixture'], cwd=live, check=True)
    subprocess.run(['git', 'config', 'user.email', 'epoch-fixture@example.invalid'], cwd=live, check=True)
    subprocess.run(['git', 'config', 'commit.gpgsign', 'false'], cwd=live, check=True)
    tree = subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=live, text=True).strip()
    orphan = subprocess.check_output(['git', 'commit-tree', tree], cwd=live, input='unrelated\n', text=True).strip()
    subprocess.run(['git', 'update-ref', 'HEAD', orphan], cwd=live, check=True)
    with pytest.raises(ValueError, match='required local Git history unavailable'):
        epoch.validate(live)


def test_unknown_or_duplicate_historical_test_names_are_refused(live):
    name = sorted(epoch.HISTORICAL_TESTS)[0]
    for selected in [[name, name], ['code/a5_fingerprint/test_unreviewed.py'], []]:
        with pytest.raises(ValueError, match='unknown or duplicate'):
            epoch.replay(live, selected)
