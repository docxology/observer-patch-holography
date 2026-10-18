"""Exact command/roster accounting for the explicit current compatibility profile."""
from pathlib import Path
import importlib.util
import sys
import pytest

ROOT = Path(__file__).resolve().parents[1]

def module(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    assert spec is not None and spec.loader is not None
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result

profile = module('oph_context_dispatch_test', 'tools/run_current_mandatory_suite.py')
owner = module('oph_original_dispatch_test', 'tools/run_mandatory_suite.py')
LIVE, CAMPAIGN, FINGERPRINT = (Path('/current'), Path('/historical-campaign'), Path('/historical-fingerprint'))


def plan(steps):
    return profile.execution_plan(steps, LIVE, CAMPAIGN, FINGERPRINT)


def test_complete_full_and_certificate_roster_retains_every_original_command():
    steps = owner.MANDATORY_STEPS + owner.CERTIFICATE_STEPS
    actual = plan(steps)
    cursor = 0
    for title, command in steps:
        count = 9 if title == profile.FINGERPRINT_TITLE else 1
        selected_rows = actual[cursor:cursor + count]
        assert all(label == title for label, _, _, _ in selected_rows)
        selected = [(cmd, cwd) for _, cmd, cwd, _ in selected_rows]
        cursor += count
        if title == profile.FINGERPRINT_TITLE:
            assert [name for cmd, _ in selected for name in cmd[4:]] == command[4:]
            assert len(selected) == 9  # Contiguous contexts preserve original order.
        else:
            assert selected == [(command, CAMPAIGN if title in {profile.VERIFY_TITLE, profile.MUTATION_TITLE} else LIVE)]
    assert cursor == len(actual)
    assert len(actual) == len(steps) + 8
    historical = [(cmd, cwd) for _, cmd, cwd, _ in actual if cwd != LIVE]
    assert len(historical) == 6
    assert sum(cwd == CAMPAIGN for _, cwd in historical) == 2
    assert [cmd[4] for cmd, cwd in historical if cwd == FINGERPRINT] == [
        name for name in profile.FINGERPRINT_FILES if name in profile.fingerprint.HISTORICAL_TESTS
    ]


def test_all_nine_standard_shards_preserve_exact_order_and_multiplicity():
    original = [step for step in owner.MANDATORY_STEPS if step[0] not in owner.HEAVY_STEP_TITLES]
    combined = []
    for index in range(9):
        combined += plan(original[len(original) * index // 9:len(original) * (index + 1) // 9])
    assert combined == plan(original)


@pytest.mark.parametrize('title', [profile.VERIFY_TITLE, profile.MUTATION_TITLE])
def test_historical_campaign_route_cannot_change_original_argv(title):
    command = next(cmd for name, cmd in owner.MANDATORY_STEPS if name == title)
    with pytest.raises(ValueError, match='invocation changed'):
        plan([(title, command + ['--help'])])


@pytest.mark.parametrize('change', ['drop', 'duplicate', 'reorder', 'unknown-current', 'unknown-historical', 'different-python'])
def test_fingerprint_routing_refuses_any_unreviewed_roster_or_prefix(change):
    command = next(list(cmd) for name, cmd in owner.MANDATORY_STEPS if name == profile.FINGERPRINT_TITLE)
    if change == 'drop':
        command.pop()
    elif change == 'duplicate':
        command[-1] = command[-2]
    elif change == 'reorder':
        command[4], command[5] = command[5], command[4]
    elif change == 'unknown-current':
        command[4] = 'code/a5_fingerprint/test_unreviewed.py'
    elif change == 'unknown-historical':
        index = next(i for i, name in enumerate(command) if name in profile.fingerprint.HISTORICAL_TESTS)
        command[index] = 'code/a5_fingerprint/test_unreviewed.py'
    else:
        command[0] = '/unreviewed-python'
    with pytest.raises(ValueError, match='changed'):
        plan([(profile.FINGERPRINT_TITLE, command)])


def test_certificate_only_commands_keep_the_current_context():
    assert all(directory == LIVE for _, _, directory, _ in plan(owner.CERTIFICATE_STEPS))
