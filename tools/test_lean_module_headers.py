"""Protect frozen certificate declarations during the module-system migration."""

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "module_headers", ROOT / "Lean/tools/module_headers.py"
)
assert SPEC is not None and SPEC.loader is not None
HEADERS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HEADERS)


def test_preamble_preserves_every_payload_byte():
    payload = (
        "\n/- frozen data, including import text -/\ndef edges := [(0, 1, true)]\n"
    )
    source = "import OphGap.Checker\nimport OphGap.Transport\n" + payload
    converted = HEADERS.module_source(source)
    assert converted == (
        "module\npublic import OphGap.Checker\npublic import OphGap.Transport\n"
        "\n@[expose] public section\n" + payload
    )
    assert HEADERS.module_source(converted) == converted


def test_generated_sources_are_public_modules():
    generated = [
        p
        for p in (ROOT / "Lean/OphGap").rglob("*.lean")
        if "AUTO-GENERATED" in p.read_text()[:2000]
    ]
    assert len(generated) == 15
    for path in generated:
        source = path.read_text()
        assert source.startswith("module\npublic import ")
        assert "\n@[expose] public section\n" in source


def test_refuses_unrecognized_preamble():
    with pytest.raises(ValueError, match="beginning with its imports"):
        HEADERS.module_source("def certificate := true\n")
