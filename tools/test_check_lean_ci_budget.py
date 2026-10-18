from __future__ import annotations

from tools.check_lean_ci_budget import LAKEFILE, WORKFLOW, validate


def _inputs() -> tuple[str, str]:
    return (
        WORKFLOW.read_text(encoding="utf-8"),
        LAKEFILE.read_text(encoding="utf-8"),
    )


def test_current_wiring_passes() -> None:
    workflow, lakefile = _inputs()
    assert validate(workflow, lakefile) == []


def test_default_ophgap_target_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = lakefile.replace(
        "lean_lib «OphGap» where",
        "@[default_target]\nlean_lib «OphGap» where",
        1,
    )
    assert "OphGap must not be a Lake default target" in validate(workflow, mutated)


def test_job_over_thirty_minutes_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("    timeout-minutes: 30", "    timeout-minutes: 31", 1)
    assert "Lean CI 'build' job exceeds the 30-minute ceiling" in validate(mutated, lakefile)


def test_golden_job_over_thirty_minutes_is_rejected() -> None:
    workflow, lakefile = _inputs()
    marker = (
        "  golden_sector_psl2f5:\n"
        "    name: Golden-sector PSL2F5 representations\n"
        "    runs-on: ubuntu-latest\n"
        "    timeout-minutes: 30"
    )
    mutated = workflow.replace(marker, marker[:-2] + "31", 1)
    assert (
        "Lean CI 'golden_sector_psl2f5' job exceeds the 30-minute ceiling"
        in validate(mutated, lakefile)
    )


def test_full_lake_cache_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("            Lean/.lake/build", "            Lean/.lake", 1)
    assert (
        "Lean CI must cache build artifacts, not the full Lake dependency tree"
        in validate(mutated, lakefile)
    )


def test_nonresumable_cache_key_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("-${{ github.run_attempt }}", "")
    errors = validate(mutated, lakefile)
    assert "Lean CI 'build' cache keys must support resumable re-runs" in errors
    assert "Lean CI 'golden_sector_psl2f5' cache keys must support resumable re-runs" in errors
    assert "Lean CI 'ophgap' cache keys must support resumable re-runs" in errors


def test_stale_core_cache_step_reference_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace(
        "steps.budget_build.outputs.status == '0' || steps.budget_build.outputs.status == '124'",
        "steps.lean_build.outcome == 'success' || steps.lean_build.outputs.timed_out == 'true'",
        1,
    )
    assert "the core Lean cache must save successful and timed-out builds using the declared budget_build status" in validate(mutated, lakefile)


def test_missing_core_build_step_id_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("        id: budget_build\n", "", 1)
    assert "the core Lean cache must save successful and timed-out builds using the declared budget_build status" in validate(mutated, lakefile)


def test_core_cache_must_preserve_timed_out_progress() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace(" || steps.budget_build.outputs.status == '124'", "", 1)
    assert "the core Lean cache must save successful and timed-out builds using the declared budget_build status" in validate(mutated, lakefile)


def test_missing_core_cache_save_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("      - name: Save Lake build cache\n", "      - name: Missing cache save\n", 1)
    assert "the core Lean cache must save successful and timed-out builds using the declared budget_build status" in validate(mutated, lakefile)


def test_golden_budget_change_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace(
        "timeout 23m lake build GoldenSectorPSL2F5Representations",
        "timeout 24m lake build GoldenSectorPSL2F5Representations",
        1,
    )
    assert (
        "the typed golden-sector bridge must retain its 23-minute resumable budget"
        in validate(mutated, lakefile)
    )


def test_golden_core_exclusion_is_required() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace(
        "Screen/OPHScreen.lean|Screen/GoldenSectorPSL2F5Representations.lean) continue ;;",
        "Screen/OPHScreen.lean) continue ;;",
        1,
    )
    assert (
        "the core Lean build must leave the import-only OPHScreen umbrella and typed golden bridge to their dedicated/nightly lanes"
        in validate(mutated, lakefile)
    )


def test_duplicate_branch_and_pr_runs_are_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("    branches: [main]\n", "", 1)
    assert "Lean CI branch pushes must be limited to main" in validate(mutated, lakefile)


def test_missing_superseded_run_cancellation_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("  cancel-in-progress: true", "  cancel-in-progress: false", 1)
    assert "Lean CI must cancel superseded runs" in validate(mutated, lakefile)


def test_exhaustive_default_build_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace('lake build "${targets[@]}"', "lake build", 1)
    errors = validate(mutated, lakefile)
    assert "per-change Lean CI must not run an exhaustive default Lake build" in errors


def test_dropped_target_collection_is_rejected() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace('targets+=("$target")', ':', 1)
    assert "changed Lean modules must build the complete nonempty target array" in validate(mutated, lakefile)


def test_empty_target_guard_is_required() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace('[ "${#targets[@]}" -gt 0 ] || exit 1', ':', 1)
    assert "changed Lean modules must build the complete nonempty target array" in validate(mutated, lakefile)


def test_mathlib_download_cache_must_save_before_proof_build() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("      - name: Save pinned Mathlib download cache before proof compilation\n", "      - name: Missing download save\n", 1)
    assert "the golden-sector dependency download cache must persist before proof compilation" in validate(mutated, lakefile)


def test_mathlib_download_cache_cannot_accept_failed_fetch() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace(" && steps.mathlib_fetch.outputs.status == '0'", "", 1)
    assert "the golden-sector dependency download cache must use exact platform/toolchain/manifest keys and successful fetch evidence" in validate(mutated, lakefile)


def test_mathlib_download_cache_keys_must_include_the_pinned_manifest() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("key: mathlib-download-v1-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles('Lean/lean-toolchain', 'Lean/lake-manifest.json') }}", "key: unpinned-mathlib", 1)
    assert "the golden-sector dependency download cache must use exact platform/toolchain/manifest keys and successful fetch evidence" in validate(mutated, lakefile)


def test_mathlib_download_cache_cannot_restore_other_toolchain_keys() -> None:
    workflow, lakefile = _inputs()
    marker = "      - name: Restore pinned Mathlib download cache\n"
    mutated = workflow.replace(marker, marker + "        restore-keys: broad-cache-prefix\n", 1)
    assert "the golden-sector dependency download cache must use exact platform/toolchain/manifest keys and successful fetch evidence" in validate(mutated, lakefile)


def test_mathlib_download_cache_directory_must_match_the_client() -> None:
    workflow, lakefile = _inputs()
    mutated = workflow.replace("MATHLIB_CACHE_DIR: ${{ runner.temp }}/oph-mathlib-downloads", "MATHLIB_CACHE_DIR: /unbound-cache", 1)
    assert "the golden-sector dependency download cache must use exact platform/toolchain/manifest keys and successful fetch evidence" in validate(mutated, lakefile)
