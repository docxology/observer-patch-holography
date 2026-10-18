#!/usr/bin/env python3
"""Independent source/permutation/sparse-witness check; no producer import."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
from itertools import product
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "Lean/QFT/SourceOperatorGeneration.lean": "a20f64d7a399c91c2380941b087f72de811a27c3613604c8d4f46c0af3472fc0",
    "Lean/QFT/TripleCarrierJoin.lean": "7997d50afc089326ec70fce55393766011aa79ac357dce4f8b5a01a9c4865539",
    "Lean/QFT/TowerAnchoredCorrelation.lean": "19025d4b686a12160eb73fbe9f005df8879d98238f6db5f3940ea0dfa1da8838",
}
DIMS = (13, 14, 13)
POINTS = tuple(product(*(range(n) for n in DIMS)))


class Rejected(ValueError):
    pass


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise Rejected(reason)


def exact_equal(actual, expected, where: str) -> None:
    """JSON booleans cannot pass as integer dimensions/counts/indices."""
    require(type(actual) is type(expected), f"{where}: type")
    if isinstance(expected, dict):
        require(actual.keys() == expected.keys(), f"{where}: fields")
        for key in expected:
            exact_equal(actual[key], expected[key], f"{where}.{key}")
    elif isinstance(expected, list):
        require(len(actual) == len(expected), f"{where}: length")
        for i, (a, b) in enumerate(zip(actual, expected)):
            exact_equal(a, b, f"{where}[{i}]")
    else:
        require(actual == expected, f"{where}: value")


def read_source(root: Path) -> tuple[list[list[int]], list[list[list[int]]]]:
    for path, digest in PINS.items():
        require(hashlib.sha256((root / path).read_bytes()).hexdigest() == digest,
                f"pinned source changed: {path}")
    text = (root / "Lean/QFT/SourceOperatorGeneration.lean").read_text(encoding="utf-8")
    paths, tables = [], []
    for observer, dimension in zip((86, 88, 247), DIMS):
        block = re.search(rf"def obs{observer}\s*:.*?(?=\n/--)", text, re.S).group()
        path_text = re.search(r"path := !\[(.*?)\]\s+cnt", block, re.S).group(1)
        path = [int(v) for v in re.findall(r"\d+", path_text)]
        table_text = block.split("cnt := fun i =>", 1)[1]
        table = [[int(v) for v in row.split(",")] for row in re.findall(r"!\[([\d,]+)\]", table_text)]
        require(len(path) == 32 and len(table) == dimension, "source dimensions")
        require(all(len(row) == dimension for row in table), "source square table")
        observed = Counter(zip(path, path[1:]))
        require(all(table[a][b] == observed[a, b]
                    for a in range(dimension) for b in range(dimension)), "source transition census")
        require(table[path[-1]][path[0]] == 0, "terminal edge must remain absent")
        paths.append(path)
        tables.append(table)
    return paths, tables


def sparse_unit(axes: tuple[int, ...], row: tuple[int, ...], col: tuple[int, ...]) -> dict:
    """Matrix-unit inclusion with exact identity on every spectator slot."""
    spectator = tuple(a for a in range(3) if a not in axes)
    result = {}
    for labels in product(*(range(DIMS[a]) for a in spectator)):
        q, r = [0] * 3, [0] * 3
        for a, x, y in zip(axes, row, col):
            q[a], r[a] = x, y
        for a, x in zip(spectator, labels):
            q[a] = r[a] = x
        result[tuple(q), tuple(r)] = 1
    return result


def multiply(left: dict, right: dict) -> dict:
    by_row = defaultdict(list)
    for (row, col), value in right.items():
        by_row[row].append((col, value))
    out = defaultdict(int)
    for (row, shared), a in left.items():
        for col, b in by_row[shared]:
            out[row, col] += a * b
    return {key: value for key, value in out.items() if value}


def sparse_controls() -> int:
    x = sparse_unit((0,), (0,), (1,))
    y = sparse_unit((0,), (1,), (0,))
    require(multiply(x, y) != multiply(y, x), "full hinge must be noncommutative")
    b = sparse_unit((1,), (0,), (1,))
    c = sparse_unit((2,), (0,), (1,))
    require(multiply(b, c) == multiply(c, b), "exclusive spectators must commute")
    # A complete triple matrix unit is a product of pair units sharing a
    # chosen intermediate hinge value. Lean proves this for every index.
    witnesses = [(POINTS[0], POINTS[-1]), (POINTS[-1], POINTS[0])]
    witnesses += [(POINTS[i], POINTS[(i * 317 + 61) % len(POINTS)])
                  for i in range(0, len(POINTS), 149)]
    for q, r in witnesses:
        left = sparse_unit((0, 1), (q[0], q[1]), (0, r[1]))
        right = sparse_unit((0, 2), (0, q[2]), (r[0], r[2]))
        require(multiply(left, right) == {(q, r): 1}, "matrix-unit generation")
    return len(witnesses)


def verify(packet: dict, root: Path = ROOT) -> dict:
    require(type(packet) is dict, "packet must be an object")
    require(set(packet) == {"schema", "parents", "carrier", "embeddings", "state", "transitions", "interpretation"},
            "packet fields")
    exact_equal(packet["schema"], "oph.source_operator_join.v1", "schema")
    exact_equal(packet["parents"], PINS, "parents")
    paths, _ = read_source(root)
    exact_equal(packet["carrier"], {
        "observers": [86, 88, 247], "slot_dimensions": [13, 14, 13],
        "pair_dimensions": [182, 169], "triple_dimension": 2366,
        "common_full_matrix_dimension": 13, "common_complex_vector_dimension": 169,
        "joint_complex_vector_dimension": 5597956}, "carrier")
    exact_equal(packet["embeddings"], {"pair88_axes": [0, 1], "pair247_axes": [0, 2],
                                     "unused_factor": "identity", "common_axes": [0]}, "embeddings")
    exact_equal(packet["interpretation"], {
        "tensor_assembly": "declared", "source_labels": "post_hoc_committed",
        "empirical_state": "source_counted_diagonal",
        "tower_state": "independent_uniform_not_identified",
        "admitted_generation": "full_source_operator_generators",
        "overlapping_pair_algebras_commute": False, "physical_regions": False,
        "physical_clock": False, "observed_quantum_outcomes": False,
        "continuum_refinement": False, "scalar64_instrument_same_carrier": False,
        "universal_algebraic_pushout": False}, "interpretation")
    triple = [tuple(p[t] for p in paths) for t in range(32)]
    def census(axes):
        ctr = Counter(tuple(q[a] for a in axes) for q in triple)
        return [list(q) + [ctr[q]] for q in sorted(ctr)]
    exact_equal(packet["state"], {"denominator": 32, "triple_counts": census((0, 1, 2)),
                                "pair88_counts": census((0, 1)),
                                "pair247_counts": census((0, 2))}, "state")
    require(type(packet["transitions"]) is list and len(packet["transitions"]) == 31,
            "exactly the 31 actual transitions")
    checked_points = 0
    prefixes = [[list(range(n)) for n in DIMS]]
    for t, transition in enumerate(packet["transitions"]):
        permutations = []
        for n, path in zip(DIMS, paths):
            a, b = path[t:t + 2]
            permutations.append([b if x == a else a if x == b else x for x in range(n)])
        exact_equal(transition, {"row": t, "next_row": t + 1, "permutations": permutations}, f"transition{t}")
        move = lambda q: tuple(permutations[a][q[a]] for a in range(3))
        require(move(triple[t]) == triple[t + 1], "source path transport")
        # Coordinate bijections and spectator preservation establish covariance
        # of every matrix-unit embedding, not just diagonal path projectors.
        for q in POINTS:
            out = move(q)
            require(out[:2] == (permutations[0][q[0]], permutations[1][q[1]]), "88 projection")
            require((out[0], out[2]) == (permutations[0][q[0]], permutations[2][q[2]]), "247 projection")
            checked_points += 1
        prefixes.append([[permutations[a][x] for x in prefixes[-1][a]] for a in range(3)])
    # Chronological finite transports, with inverse prefixes, are coherent on
    # all 496 nonempty row intervals. No terminal-to-initial transition is used.
    interval_count = 0
    for start in range(32):
        inverse = [[prefixes[start][a].index(x) for x in range(n)] for a, n in enumerate(DIMS)]
        running = [list(range(n)) for n in DIMS]
        for end in range(start + 1, 32):
            step = packet["transitions"][end - 1]["permutations"]
            running = [[step[a][x] for x in running[a]] for a in range(3)]
            direct = [[prefixes[end][a][inverse[a][x]] for x in range(n)] for a, n in enumerate(DIMS)]
            require(running == direct, "chronological transport composition")
            require(tuple(direct[a][triple[start][a]] for a in range(3)) == triple[end], "interval path")
            interval_count += 1
    samples = sparse_controls()
    return {"verdict": "verified_source_operator_join_packet",
            "source_rows": 32, "actual_transitions": 31,
            "transition_carrier_points": checked_points, "chronological_intervals": interval_count,
            "sparse_matrix_unit_witnesses": samples,
            "physical_adequacy": False, "observed_quantum_outcomes": False,
            "lean_kernel_replay_performed": False,
            "universal_operator_theorems_verified_by_python": False}


def load(path: Path) -> dict:
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f"duplicate key: {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(load(args.packet)), sort_keys=True, indent=2))
