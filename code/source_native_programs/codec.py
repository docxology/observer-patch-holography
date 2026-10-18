"""Serialization and custody; no shared routing, execution or decoding."""
import hashlib
from pathlib import Path
import re

from source_read_acceptance.codec import canonical, compact, digest, equal, load, load_artifact

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SUPPORTS = {3: "code/source_routing/support_w12_l3.json",
            4: "code/source_read_routing/support_w12_l4.json",
            5: "code/source_read_routing/support_w12_l5.json"}


def proof_paths():
    pending, paths = ["Geometry.SourceNativeProgramsAxiomAudit"], set()
    while pending:
        path = "Lean/"+pending.pop().replace(".", "/")+".lean"
        if path in paths or not (ROOT/path).is_file():
            continue
        paths.add(path)
        for line in re.findall(r"^(?:public )?import (.+)$", (ROOT/path).read_text(encoding="utf-8"), re.M):
            pending.extend(line.split())
    return paths


def pins():
    paths = proof_paths() | set(SUPPORTS.values()) | {
        "Lean/lean-toolchain", "Lean/lakefile.lean", "Lean/lake-manifest.json",
        "docs/AXIOM_REFERENCE.md", "claims/axiom_registry.yaml",
        "code/source_read_acceptance/codec.py", "code/source_read_acceptance/__init__.py",
        "evidence/source_net_causal_poset/build_causal_poset.py",
        "evidence/source_net_causal_poset/carrier_source_net_receipt.json",
        "code/source_read_routing/controls/q3_baseline.json",
        *(f"code/source_native_programs/{name}" for name in (
            "__init__.py", "codec.py", "routes.py", "check_routes.py", "build.py",
            "verify.py", "family_build.py", "family_verify.py", "lean_control.py", "CONTRACT.md")),
    }
    return {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}
