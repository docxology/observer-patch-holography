"""Verify the captured simulator operations, local proofs, and emitted receipt."""
import argparse
import hashlib
from pathlib import Path
import re

from . import simulator_verifier as check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def pins():
    names = {p.relative_to(ROOT).as_posix() for p in HERE.iterdir()
             if p.suffix in (".py", ".md")}
    names.update({"code/source_operation_reads/source_snapshot.json",
                  "docs/AXIOM_REFERENCE.md", "claims/axiom_registry.yaml",
                  "Lean/lean-toolchain", "Lean/lakefile.lean", "Lean/lake-manifest.json"})
    pending = ["Geometry.SourceOperationReadsAxiomAudit"]
    while pending:
        name = "Lean/"+pending.pop().replace(".", "/")+".lean"
        path = ROOT/name
        if name in names or not path.is_file():
            continue
        names.add(name)
        for imports in re.findall(r"^(?:public )?import (.+)$", path.read_text(encoding="utf-8"), re.M):
            pending.extend(imports.split())
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sorted(names)}


def verify(packet):
    source = check.strict_load(HERE/"source_snapshot.json")
    if type(packet) is not dict:
        raise ValueError("packet object")
    check.equal(packet.get("source"), source, "frozen source identity")
    # This is a byte-identical copy of the companion simulator verifier.
    check.equal(hashlib.sha256((HERE/"simulator_verifier.py").read_bytes()).hexdigest(),
                source["files"]["oph_fpe/bulk/verify_primitive_source_reads_independent.py"],
                "independent verifier source pin")
    result = check.verify(packet)
    return {"schema": 1, "source_pins": pins(), "native_derivation": result,
            "M1_derived": False, "complete_A1_A3_model": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, default=HERE/"capture.json")
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    result = verify(check.strict_load(args.packet))
    if args.write_receipt:
        (HERE/"receipt.json").write_bytes(check.canonical(result))
    else:
        check.equal(result, check.strict_load(HERE/"receipt.json"), "receipt")
    print(check.canonical({"verified": True, "capture_sha256": result["native_derivation"]["packet_sha256"],
                           "source_revision": check.strict_load(HERE/"source_snapshot.json")["revision"],
                           "M1_derived": False}).decode("ascii"), end="")


if __name__ == "__main__":
    main()
