"""Real Git and working-byte controls for preserved frozen Lean epochs."""

import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "frozen_source_epoch_guard", ROOT / "tools/build_fz_registry.py"
)
guard = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = guard
spec.loader.exec_module(guard)
KEYS = tuple(guard.LEAN435_CUSTODY_SOURCE_PAIRS)


@pytest.fixture
def isolated(tmp_path, monkeypatch):
    clone = tmp_path / "source"
    subprocess.run(
        ["git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT), str(clone)],
        check=True,
    )
    for _, relative in KEYS:
        path = clone / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, path)
    monkeypatch.setattr(guard, "ROOT", clone)
    return clone


@pytest.mark.parametrize("key", KEYS)
def test_exact_ancestral_source_blobs_pass(isolated, key):
    assert guard.verify_preserved_lean_source_epoch(
        *key, guard.LEAN435_CUSTODY_SOURCE_PAIRS[key][1]
    )


@pytest.mark.parametrize("key", KEYS)
def test_changed_current_bytes_reject(isolated, key):
    path = isolated / key[1]
    path.write_bytes(path.read_bytes() + b"\n-- unreviewed drift\n")
    assert not guard.verify_preserved_lean_source_epoch(
        *key, guard.LEAN435_CUSTODY_SOURCE_PAIRS[key][1]
    )


@pytest.mark.parametrize("key", KEYS)
def test_changed_frozen_hash_rejects(isolated, key):
    assert not guard.verify_preserved_lean_source_epoch(*key, "0" * 64)


def test_no_git_export_cannot_supply_ancestral_source_evidence(isolated):
    shutil.rmtree(isolated / ".git")
    key = KEYS[0]
    with pytest.raises(SystemExit, match="requires exact ancestral Git history"):
        guard.verify_preserved_lean_source_epoch(
            *key, guard.LEAN435_CUSTODY_SOURCE_PAIRS[key][1]
        )


def test_missing_frozen_commit_rejects(isolated, monkeypatch):
    key = KEYS[0]
    _, frozen, current = guard.LEAN435_CUSTODY_SOURCE_PAIRS[key]
    monkeypatch.setitem(
        guard.LEAN435_CUSTODY_SOURCE_PAIRS, key, ("0" * 40, frozen, current)
    )
    with pytest.raises(SystemExit, match="commit does not resolve"):
        guard.verify_preserved_lean_source_epoch(*key, frozen)


def test_rehashed_current_metadata_cannot_replace_immutable_blob(isolated, monkeypatch):
    key = KEYS[0]
    path = isolated / key[1]
    path.write_bytes(path.read_bytes() + b"\n-- coherent rehash attack\n")
    commit, frozen, _ = guard.LEAN435_CUSTODY_SOURCE_PAIRS[key]
    monkeypatch.setitem(
        guard.LEAN435_CUSTODY_SOURCE_PAIRS,
        key,
        (commit, frozen, guard.sha256_file(path)),
    )
    with pytest.raises(SystemExit, match="historical blob hash mismatch"):
        guard.verify_preserved_lean_source_epoch(*key, frozen)


def test_missing_maintained_commit_rejects(isolated, monkeypatch):
    monkeypatch.setattr(guard, "LEAN435_CUSTODY_SOURCE_COMMIT", "0" * 40)
    key = KEYS[0]
    with pytest.raises(SystemExit, match="commit does not resolve"):
        guard.verify_preserved_lean_source_epoch(
            *key, guard.LEAN435_CUSTODY_SOURCE_PAIRS[key][1]
        )


def test_missing_current_file_rejects(isolated):
    key = KEYS[0]
    (isolated / key[1]).unlink()
    assert not guard.verify_preserved_lean_source_epoch(
        *key, guard.LEAN435_CUSTODY_SOURCE_PAIRS[key][1]
    )


def test_receipt_has_no_lean_migration_exception(isolated):
    assert not guard.verify_preserved_lean_source_epoch(
        "FZ-02",
        "code/a5_closure/receipts/a5_angular_multiplet_reference.receipt.json",
        "0" * 64,
    )


def test_real_unrelated_commit_cannot_supply_maintained_epoch(isolated, monkeypatch):
    tree = subprocess.check_output(
        ["git", "rev-parse", guard.LEAN435_CUSTODY_SOURCE_COMMIT + "^{tree}"],
        cwd=isolated,
        text=True,
    ).strip()
    orphan = subprocess.check_output(
        [
            "git",
            "-c",
            "user.name=Custody test",
            "-c",
            "user.email=custody-test@example.invalid",
            "commit-tree",
            tree,
            "-m",
            "Unrelated test source epoch",
        ],
        cwd=isolated,
        text=True,
    ).strip()
    monkeypatch.setattr(guard, "LEAN435_CUSTODY_SOURCE_COMMIT", orphan)
    key = KEYS[0]
    with pytest.raises(SystemExit, match="not an ancestor of HEAD"):
        guard.verify_preserved_lean_source_epoch(
            *key, guard.LEAN435_CUSTODY_SOURCE_PAIRS[key][1]
        )
