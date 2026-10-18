#!/usr/bin/env python3
"""Run the current compatibility profile with explicit historical frozen replays.

The byte-frozen owner driver supplies every command and all CLI/shard selection.
Only two sealed-campaign commands and four immutable fingerprint test files run
against historical Git blobs. The original live verifiers are not changed.
"""
from __future__ import annotations
from contextlib import ExitStack
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
VERIFY_TITLE = 'Validate the invariant-mining pre-generation source lock'
MUTATION_TITLE = 'Execute the invariant-mining pre-generation mutation gates'
FINGERPRINT_TITLE = 'Execute the A5 fingerprint and frozen primitive-port prediction suites'
FINGERPRINT_FILES = ('code/a5_fingerprint/test_a5_multipole_fixed_point_certificate.py',
 'code/a5_fingerprint/test_a5_multipole_fixed_point_hardening_certificate.py',
 'code/a5_fingerprint/test_a5_multipole_persistence_certificate.py',
 'code/a5_fingerprint/test_a5_multipole_persistence_independent_verifier.py',
 'code/a5_fingerprint/test_a5_multipole_persistence_stage4_certificate.py',
 'code/a5_fingerprint/test_a5_multipole_persistence_stage4_independent_verifier.py',
 'code/a5_fingerprint/test_spin_six_universality_certificate.py',
 'code/a5_fingerprint/test_spin_six_primitive_port_prediction.py',
 'code/a5_fingerprint/test_seam_current_edge_prediction.py',
 'code/a5_fingerprint/test_fz12_observation_map_certificate.py',
 'code/a5_fingerprint/test_fz12_full_symbol_remainder_certificate.py',
 'code/a5_fingerprint/test_fz12_synthetic_recovery_coverage.py',
 'code/a5_fingerprint/test_fz12_free_photon_hamiltonian.py',
 'code/a5_fingerprint/test_fz12_auger_threshold_diagnostic.py',
 'code/a5_fingerprint/test_carrier_scale_bound_diagnostic.py',
 'code/a5_fingerprint/test_carrier_frequency_speed_certificate.py',
 'code/a5_fingerprint/test_carrier_class_dispersion_certificate.py',
 'code/a5_fingerprint/test_differentiator_inventory_certificate.py',
 'code/a5_fingerprint/test_fz11_decision_rule_v2_sibling.py')


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError('local profile module unavailable: ' + str(path))
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


invariant = load_module('oph_current_invariant_epoch', ROOT / 'tools/replay_invariant_mining_epoch.py')
fingerprint = load_module('oph_current_fingerprint_epoch', ROOT / 'tools/replay_fingerprint_epoch.py')


def fingerprint_segments(command: list[str], live: Path, historical: Path):
    invariant.require(command[:4] == [sys.executable, '-m', 'pytest', '-q'],
                      'frozen fingerprint invocation changed')
    tests = command[4:]
    invariant.require(tuple(tests) == FINGERPRINT_FILES, 'frozen fingerprint test roster changed')
    invariant.require(len(tests) == len(set(tests)) and len(tests) == 19,
                      'frozen fingerprint test census changed')
    invariant.require(set(tests) & fingerprint.HISTORICAL_TESTS == fingerprint.HISTORICAL_TESTS,
                      'historical fingerprint test membership changed')
    segments: list[tuple[list[str], Path, str]] = []
    for test in tests:
        directory = historical if test in fingerprint.HISTORICAL_TESTS else live
        label = 'historical fingerprint ' + fingerprint.HISTORICAL_EPOCH if directory == historical else 'current worktree'
        if segments and segments[-1][1] == directory:
            segments[-1][0].append(test)
        else:
            segments.append((command[:4] + [test], directory, label))
    invariant.require([name for cmd, _, _ in segments for name in cmd[4:]] == tests,
                      'fingerprint dispatch dropped, duplicated or reordered a file')
    return segments


def execution_plan(steps, live: Path, campaign: Path, historical_fingerprint: Path):
    result = []
    for title, raw_command in steps:
        command = list(raw_command)
        if title == VERIFY_TITLE:
            invariant.require(command == [sys.executable, 'code/invariant_mining/tools/verify_pregeneration_freeze_independent.py'],
                              'frozen campaign verifier invocation changed')
            routes = [(command, campaign, 'historical invariant campaign ' + invariant.HISTORICAL_EPOCH)]
        elif title == MUTATION_TITLE:
            invariant.require(command == [sys.executable, '-m', 'pytest', '-q', 'code/invariant_mining/tests/test_pregeneration_lock.py'],
                              'frozen campaign mutation invocation changed')
            routes = [(command, campaign, 'historical invariant campaign ' + invariant.HISTORICAL_EPOCH)]
        elif title == FINGERPRINT_TITLE:
            routes = fingerprint_segments(command, live, historical_fingerprint)
        else:
            routes = [(command, live, 'current worktree')]
        result.extend((title, cmd, directory, label) for cmd, directory, label in routes)
    return result


def main() -> None:
    campaign_context = invariant.validate(ROOT)
    fingerprint_context = fingerprint.validate(ROOT)
    # validate() already requires the exact original driver as a historical
    # control document. Import it only after this byte/history check succeeds.
    owner = load_module('oph_byte_frozen_mandatory_owner', ROOT / 'tools/run_mandatory_suite.py')
    for title in (VERIFY_TITLE, MUTATION_TITLE, FINGERPRINT_TITLE):
        invariant.require(sum(item[0] == title for item in owner.MANDATORY_STEPS) == 1,
                          'frozen contextual step identity changed')
    with ExitStack() as stack:
        campaign = invariant.materialize(campaign_context, Path(stack.enter_context(tempfile.TemporaryDirectory(prefix='oph-current-campaign-'))))
        historic_fingerprint = invariant.materialize(fingerprint_context, Path(stack.enter_context(tempfile.TemporaryDirectory(prefix='oph-current-fingerprint-'))))
        print('CURRENT COMPATIBILITY PROFILE: live worktree plus explicit byte-frozen historical replays.', flush=True)
        print('Original live source-drift guards and frozen records remain unchanged.', flush=True)

        def run_steps(steps):
            for title, command, directory, label in execution_plan(steps, ROOT, campaign, historic_fingerprint):
                print('==> ' + title + ' [source context: ' + label + ']', flush=True)
                environment = None
                if directory != ROOT:
                    environment = os.environ.copy()
                    environment['PYTHONPATH'] = str(directory / 'code')
                    environment['PYTHONDONTWRITEBYTECODE'] = '1'
                result = subprocess.run(command, cwd=directory, env=environment)
                if result.returncode:
                    raise SystemExit(f'FAILED: {title} [{label}] (exit {result.returncode})')
                if directory == campaign:
                    invariant.assert_capsule(campaign_context, campaign)
                elif directory == historic_fingerprint:
                    invariant.assert_capsule(fingerprint_context, historic_fingerprint)
        owner.run_steps = run_steps
        owner.main()
        invariant.validate(ROOT)
        fingerprint.validate(ROOT)
        print('Completed CURRENT COMPATIBILITY PROFILE; historical replays are not live generation authorization.', flush=True)

if __name__ == '__main__':
    try:
        main()
    except ValueError as error:
        raise SystemExit(str(error)) from error
