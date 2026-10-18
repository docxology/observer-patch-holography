"""Serialization and custody only; no observation or acceptance algorithm."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SUPPORT = "code/source_routing/support_w12_l3.json"
TARGETS = ((1, 0), (0, 1), (1, 1), (1, -1))


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       allow_nan=False, ensure_ascii=True)+"\n").encode("ascii")


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate key")
        result[key] = value
    return result


def reject(value):
    raise ValueError(f"noninteger JSON number: {value}")


def load(path):
    return json.loads(Path(path).read_text(encoding="ascii"), object_pairs_hook=unique,
                      parse_float=reject, parse_constant=reject)


def equal(a, b, label):
    if canonical(a) != canonical(b):
        raise ValueError(label)


def pins():
    names = {SUPPORT, "docs/AXIOM_REFERENCE.md", "claims/axiom_registry.yaml",
             "Lean/lean-toolchain", "Lean/lakefile.lean", "Lean/lake-manifest.json"}
    names.update("code/source_temporal_acceptance/"+f for f in
                 ("__init__.py", "codec.py", "build.py", "verify.py", "tomography.py",
                  "check_tomography.py", "CONTRACT.md"))
    pending = ["Geometry.SourceTemporalAcceptanceAxiomAudit"]
    while pending:
        relative = "Lean/"+pending.pop().replace(".", "/")+".lean"
        path = ROOT/relative
        if relative in names or not path.is_file():
            continue
        names.add(relative)
        for line in re.findall(r"^(?:public )?import (.+)$", path.read_text(encoding="utf-8"), re.M):
            pending.extend(line.split())
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sorted(names)}
