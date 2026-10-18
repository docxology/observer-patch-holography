"""Exercise real transitive custody through Lean 4.35 public imports."""
from pathlib import Path
import importlib
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))


class PublicImportCustody(unittest.TestCase):
    def test_transitive_scalar_source_is_bound_by_every_controller(self):
        # These are real grandchildren of the audit roots, not regex fixtures.
        for package in (
            "source_checkpoint_selection", "source_native_accumulator",
            "source_native_programs", "source_publication_selection",
            "source_read_acceptance", "source_temporal_acceptance",
        ):
            with self.subTest(package=package):
                codec = importlib.import_module(package + ".codec")
                pins = codec.pins()
                self.assertIn("Lean/Geometry/SourceEncodedMemory.lean", pins)
                self.assertIn("Lean/ObserverPatchHolography/ScalarSeamRepair.lean", pins)


if __name__ == "__main__":
    unittest.main()
