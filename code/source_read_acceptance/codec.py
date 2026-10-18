"""Serialization and source custody only; no controller or replay logic."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SUPPORT = "code/source_routing/support_w12_l3.json"


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def canonical(value):
    def render(item, depth):
        if isinstance(item, dict):
            entries = ["  "*(depth+1)+compact(k)+": "+render(v,depth+1)
                       for k,v in sorted(item.items())]
            return "{\n"+",\n".join(entries)+"\n"+"  "*depth+"}"
        if isinstance(item, list) and any(isinstance(x,(list,dict)) for x in item):
            return "[\n"+",\n".join("  "*(depth+1)+render(x,depth+1) for x in item)+"\n"+"  "*depth+"]"
        return compact(item)
    return (render(value,0)+"\n").encode("ascii")


def digest(value):
    return hashlib.sha256((compact(value)+"\n").encode("ascii")).hexdigest()


def equal(actual, expected, label):
    if compact(actual) != compact(expected):
        raise ValueError(label)


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def reject(value):
    raise ValueError(f"nonintegral JSON number: {value}")


def load(path):
    return json.loads(Path(path).read_text(encoding="ascii"), object_pairs_hook=unique,
                      parse_float=reject, parse_constant=reject)


def load_artifact(path):
    value = load(path)
    if Path(path).read_bytes() != canonical(value):
        raise ValueError("noncanonical artifact bytes")
    return value


def proof_paths():
    pending = ["Geometry.SourceReadAcceptanceAxiomAudit"]
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
        *(f"code/source_read_acceptance/{name}" for name in (
            "__init__.py", "codec.py", "build.py", "verify.py", "CONTRACT.md")),
    }
    return {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}
