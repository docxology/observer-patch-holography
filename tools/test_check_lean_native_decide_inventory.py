from collections import Counter
from pathlib import Path

from tools.check_lean_native_decide_inventory import inventory, lean_code


def test_inline_native_decision_is_counted(tmp_path: Path) -> None:
    (tmp_path / "Inline.lean").write_text("example : True := by native_decide\n")
    assert inventory(tmp_path) == Counter({"Inline.lean": 1})


def test_comments_and_literals_do_not_count(tmp_path: Path) -> None:
    (tmp_path / "Data.lean").write_text(
        "-- native_decide\n/- outer /- native_decide -/ native_decide -/\n"
        '#eval "native_decide\\" native_decide"\n'
        '#eval r##"a " native_decide "# and native_decide"##\n'
        "#eval '\"'\n"
        'def native_decider := "native_decide"\n'
    )
    assert inventory(tmp_path) == Counter()


def test_tactic_quotation_is_counted(tmp_path: Path) -> None:
    (tmp_path / "Quoted.lean").write_text(
        'macro "my_decision" : tactic => `(tactic| native_decide)\n'
    )
    assert inventory(tmp_path) == Counter({"Quoted.lean": 1})


def test_dependency_tree_is_excluded(tmp_path: Path) -> None:
    dependency = tmp_path / ".lake" / "packages" / "mathlib"
    dependency.mkdir(parents=True)
    (dependency / "External.lean").write_text("example : True := by native_decide\n")
    assert inventory(tmp_path) == Counter()


def test_mask_preserves_source_locations() -> None:
    source = 'example := "/-"\n/- nested /- x -/ y -/\nnative_decide\n'
    masked = lean_code(source)
    assert len(masked) == len(source)
    assert [i for i, c in enumerate(masked) if c == "\n"] == [
        i for i, c in enumerate(source) if c == "\n"
    ]
    assert masked.count("native_decide") == 1


def test_raw_literal_does_not_hide_following_code(tmp_path: Path) -> None:
    source = r"""#eval r"literal \"
example : True := by native_decide
"""
    (tmp_path / "Raw.lean").write_text(source)
    assert inventory(tmp_path) == Counter({"Raw.lean": 1})
