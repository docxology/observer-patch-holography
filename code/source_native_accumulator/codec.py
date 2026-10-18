"""Serialization and source custody only; no shared execution or decoder."""
import hashlib
from pathlib import Path
import re

from source_read_acceptance.codec import canonical, compact, digest, equal, load, load_artifact

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SUPPORT = "code/source_routing/support_w12_l3.json"


def proof_paths():
    pending = ["Geometry.SourceAccumulatorAxiomAudit"]
    paths = set()
    while pending:
        path = "Lean/"+pending.pop().replace(".", "/")+".lean"
        if path in paths or not (ROOT/path).is_file():
            continue
        paths.add(path)
        for line in re.findall(r"^(?:public )?import (.+)$", (ROOT/path).read_text(encoding="utf-8"), re.M):
            pending.extend(line.split())
    return paths


def pins():
    paths = proof_paths() | {
        SUPPORT, "Lean/lean-toolchain", "Lean/lakefile.lean", "Lean/lake-manifest.json",
        "docs/AXIOM_REFERENCE.md", "claims/axiom_registry.yaml",
        "code/source_read_acceptance/codec.py",
        "code/source_read_acceptance/__init__.py",
        *(f"code/source_native_accumulator/{name}" for name in (
            "__init__.py", "codec.py", "build.py", "verify.py", "CONTRACT.md")),
    }
    return {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}
