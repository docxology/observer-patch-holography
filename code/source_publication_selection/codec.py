"""Serialization, fixed experiment contract and source custody only."""
import hashlib
from pathlib import Path
import re

from source_temporal_acceptance.codec import canonical, digest, equal, load

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WEIGHTS = ((1, 1, 1), (1, 2, 3), (5, 2, 1))
HORIZON = 8
QS = (5, 13, 21)
QUANTUM_CASES = ((3, 4, 5), (5, 12, 13), (8, 15, 17))
INTERVAL_CASES = tuple((N, K) for N in (1, 2, 5, 13) for K in (1, 2, 7))
STENCIL_CASES = tuple((q, exponent) for q in (4, 8, 12) for exponent in (1, 2))
PATH_CASES = ((3, (0, 2), 8), (5, (0, 2, 4), 6), (7, (0, 2, 4, 6), 4),
              (9, (0, 2, 4, 6, 8), 3), (5, (0, 1), 6), (7, (2, 3), 4))
SCOPE = {
    "native": "isolated four-port path; two independent real preparations; retained receiver samples",
    "path_invariant": "isolated adjacent means; two through five real preparation coordinates; all maximal minors",
    "law": "reference conditioned on eventual publication of both records",
    "geometry": "declared golden and uniform cube populations; ordinary Euclidean distance",
    "radius_exponents": ["1/4", "1/2", "3/4"],
    "locality": "complete-read intervals and fixed Euclidean grid stencils; no full-axiom countermodel",
    "state_selection": "analytic finite Umegaki support theorem; exact noncommuting state and declared process controls",
    "all_axioms_instantiated": False,
    "meaning_population_radius_selected": False,
    "M1_derived": False,
}


def pins():
    names = {"docs/AXIOM_REFERENCE.md", "claims/axiom_registry.yaml",
             "Lean/lean-toolchain", "Lean/lakefile.lean", "Lean/lake-manifest.json",
             "code/source_temporal_acceptance/codec.py",
             "code/source_temporal_acceptance/__init__.py"}
    names.update(str(p.relative_to(ROOT)).replace("\\", "/") for p in HERE.iterdir()
                 if p.suffix in (".py", ".md"))
    pending = ["Geometry.SourcePublicationAxiomAudit"]
    while pending:
        name = "Lean/"+pending.pop().replace(".", "/")+".lean"
        path = ROOT/name
        if name in names or not path.is_file():
            continue
        names.add(name)
        for line in re.findall(r"^(?:public )?import (.+)$", path.read_text(encoding="utf-8"), re.M):
            pending.extend(line.split())
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sorted(names)}


def seal(packet):
    return {**packet, "sha256": digest(packet)}
