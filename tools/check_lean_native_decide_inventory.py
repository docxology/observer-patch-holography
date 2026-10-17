#!/usr/bin/env python3
"""Lock the compiler-trusted ``native_decide`` inventory in the Lean tree.

The proofs in this inventory are admission-free, but Lean reports generated
native-code evaluation axioms for them. Any change must be reviewed together
with the public trust-boundary wording.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO_ROOT / "Lean"

EXPECTED = Counter(
    {
        "Screen/PortGramA5Isometry.lean": 6,
        "Screen/PortGramRepairCovariance.lean": 7,
    }
)

NATIVE_TOKEN_RE = re.compile(r"(?<![\w'])native_decide(?![\w'])")


def lean_code(text: str) -> str:
    """Mask comments and literals before locating native-decision tokens."""
    out = list(text)
    size = len(text)
    i = 0

    def blank(start: int, end: int) -> None:
        for j in range(start, end):
            if out[j] != "\n":
                out[j] = " "

    while i < size:
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = size if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < size and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif (
            text[i] == "r"
            and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'"))
            and (raw := re.match(r'r(#*)"', text[i:]))
        ):
            end = text.find('"' + raw[1], i + len(raw[0]))
            i = size if end < 0 else end + 1 + len(raw[1])
        elif text[i] == '"':
            i += 1
            while i < size:
                if text[i] == "\\":
                    i = min(size, i + 2)
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text[i] == "'" and (char := re.match(r"'(?:\\.|[^'\\\n])'", text[i:])):
            i += len(char[0])
        else:
            i += 1
            continue
        blank(start, i)
    return "".join(out)


def inventory(root: Path | None = None) -> Counter[str]:
    root = LEAN_ROOT if root is None else root
    found: Counter[str] = Counter()
    for path in sorted(root.rglob("*.lean")):
        if any(part.startswith(".") for part in path.relative_to(root).parts):
            continue
        count = len(
            NATIVE_TOKEN_RE.findall(lean_code(path.read_text(encoding="utf-8")))
        )
        if count:
            found[str(path.relative_to(root))] = count
    return found


def main() -> int:
    found = inventory()
    total = sum(found.values())
    print(f"Lean native_decide proof inventory: {total}")
    for path, count in sorted(found.items()):
        print(f"  {path}: {count}")
    if found != EXPECTED:
        print("FAIL: native_decide trust inventory changed", file=sys.stderr)
        print(f"expected: {dict(sorted(EXPECTED.items()))}", file=sys.stderr)
        print(f"found:    {dict(sorted(found.items()))}", file=sys.stderr)
        return 1
    print("OK: compiler-trusted proof inventory matches the reviewed set")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
