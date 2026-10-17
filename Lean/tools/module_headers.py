"""Own Lean module preambles while preserving generated certificate payloads.

The data producers retain ownership of every declaration after the imports.
This migration only changes the module/import preamble and exposes those
existing declarations for Lean 4.35's module system.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


def module_source(source: str) -> str:
    """Return a public module without rewriting any certificate declaration."""
    if source.startswith("module\n"):
        return source
    lines = source.splitlines(keepends=True)
    stop = 0
    while stop < len(lines) and re.fullmatch(
        r"import [A-Za-z0-9_.]+\s*\n?", lines[stop]
    ):
        stop += 1
    if not stop:
        raise ValueError("Expected a generated file beginning with its imports")
    imports = "".join("public " + line for line in lines[:stop])
    payload = "".join(lines[stop:])
    return "module\n" + imports + "\n@[expose] public section\n" + payload


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    rows = []
    for path in args.paths:
        before = path.read_text(encoding="utf-8")
        after = module_source(before)
        if args.write and before != after:
            path.write_text(after, encoding="utf-8")
        rows.append(
            {
                "path": str(path),
                "changed": before != after,
                "before_sha256": hashlib.sha256(before.encode()).hexdigest(),
                "after_sha256": hashlib.sha256(after.encode()).hexdigest(),
            }
        )
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
