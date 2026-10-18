"""Real-Git falsifiers for explicit archival campaign replay."""
from pathlib import Path
import importlib.util
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('oph_invariant_epoch_audit', ROOT / 'tools/replay_invariant_mining_epoch.py')
assert spec is not None and spec.loader is not None
epoch = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = epoch
spec.loader.exec_module(epoch)


def git(root, *args, text=None):
    return subprocess.check_output(['git', '-C', str(root), *args], input=text, text=True).strip()


@pytest.fixture(scope='module')
def source_context():
    return epoch.validate(ROOT)


@pytest.fixture
def live(tmp_path, source_context):
    root = tmp_path / 'live'
    subprocess.run(['git', 'clone', '--shared', '--no-checkout', str(ROOT), str(root)],
                   check=True, capture_output=True)
    for name in source_context['files']:
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / name).read_bytes())
    for name in ['Lean/lean-toolchain', 'Lean/lakefile.lean', 'Lean/lake-manifest.json']:
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / name).read_bytes())
    return root


def test_actual_historical_independent_verifier_passes(live, tmp_path):
    context = epoch.validate(live)
    assert len(context['source_pairs']) == 9
    capsule = epoch.materialize(context, tmp_path / 'historical')
    result = subprocess.run(epoch.commands('verify')[0], cwd=capsule,
                            capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    epoch.assert_capsule(context, capsule)
    assert all((capsule / name).read_bytes() != (live / name).read_bytes()
               for name in epoch.LEAN_PAIRS)


@pytest.mark.parametrize('name', sorted(epoch.LEAN_PAIRS))
def test_unreviewed_current_lean_bytes_cannot_use_archival_exception(live, name):
    path = live / name
    path.write_bytes(path.read_bytes() + b'\n-- unreviewed drift\n')
    with pytest.raises(epoch.EpochError, match='current Lean source drift'):
        epoch.validate(live)


def test_frozen_control_changes_are_refused(live):
    path = live / 'code/invariant_mining/policy/pregeneration_policy.json'
    path.write_bytes(path.read_bytes() + b'\n')
    with pytest.raises(epoch.EpochError, match='frozen campaign bytes changed'):
        epoch.validate(live)


def test_coherent_projection_and_freeze_reseal_is_not_historical(live):
    for name in ['build_source_projection', 'build_pregeneration_freeze']:
        result = subprocess.run([sys.executable, 'code/invariant_mining/tools/' + name + '.py'],
                                cwd=live, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
    with pytest.raises(epoch.EpochError, match='frozen projection changed'):
        epoch.validate(live)


def test_added_comparison_payload_is_refused(live):
    (live / 'code/invariant_mining/outputs/unreviewed_target.csv').write_text('target,value\nx,1\n')
    with pytest.raises(epoch.EpochError, match='frozen campaign inventory changed'):
        epoch.validate(live)


def test_shallow_history_cannot_supply_false_ancestry(live):
    (live / '.git/shallow').write_text(git(live, 'rev-parse', 'HEAD') + '\n')
    with pytest.raises(epoch.EpochError, match='required local Git history unavailable'):
        epoch.validate(live)


def test_objects_present_without_real_ancestry_are_refused(live):
    git(live, 'config', 'user.name', 'Epoch fixture')
    git(live, 'config', 'user.email', 'epoch-fixture@example.invalid')
    git(live, 'config', 'commit.gpgsign', 'false')
    orphan = git(live, 'commit-tree', git(live, 'rev-parse', 'HEAD^{tree}'), text='Unrelated test root\n')
    git(live, 'update-ref', 'HEAD', orphan)
    with pytest.raises(epoch.EpochError, match='required local Git history unavailable'):
        epoch.validate(live)


def test_no_git_working_copy_is_not_historical(live, tmp_path, source_context):
    root = tmp_path / 'no-git'
    for name in source_context['files']:
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((live / name).read_bytes())
    with pytest.raises(epoch.EpochError, match='required local Git history unavailable'):
        epoch.validate(root)


def test_materialized_source_changes_are_refused(live, tmp_path):
    context = epoch.validate(live)
    capsule = epoch.materialize(context, tmp_path / 'historical')
    path = capsule / next(iter(epoch.LEAN_PAIRS))
    path.write_bytes(path.read_bytes() + b'\n')
    with pytest.raises(epoch.EpochError, match='historical capsule changed'):
        epoch.assert_capsule(context, capsule)


def test_capsule_cannot_overwrite_live_sources(live):
    context = epoch.validate(live)
    with pytest.raises(epoch.EpochError, match='outside the live repository'):
        epoch.materialize(context, live / 'unsafe-capsule')


def test_capsule_cannot_gain_unreviewed_payload(live, tmp_path):
    context = epoch.validate(live)
    capsule = epoch.materialize(context, tmp_path / 'capsule-extra-payload')
    (capsule / 'unreviewed.csv').write_text('target,value\nx,1\n')
    with pytest.raises(epoch.EpochError, match='historical capsule inventory changed'):
        epoch.assert_capsule(context, capsule)
