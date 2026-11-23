import copy
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("coverage_gate", ROOT / "scripts/check_coverage.py")
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((ROOT / "verification/coverage.json").read_text())

    def test_should_cover_every_child_when_ledger_is_current(self):
        counts = GATE.validate_ledger(self.data)
        self.assertEqual(sum(counts.values()), 160)
        self.assertEqual(counts["unmodeled"], 0)
        self.assertEqual(counts["tested-policy"], 0)

    def test_should_reject_missing_obligation_when_row_is_removed(self):
        self.data["obligations"].pop()
        with self.assertRaisesRegex(ValueError, "match the inventory"):
            GATE.validate_ledger(self.data)

    def test_should_reject_duplicate_obligation_when_row_is_copied(self):
        self.data["obligations"].append(copy.deepcopy(self.data["obligations"][0]))
        with self.assertRaisesRegex(ValueError, "match the inventory"):
            GATE.validate_ledger(self.data)

    def test_should_reject_unknown_status_when_evidence_is_promoted(self):
        self.data["obligations"][0]["status"] = "fully-verified"
        with self.assertRaisesRegex(ValueError, "invalid status"):
            GATE.validate_ledger(self.data)

    def test_should_reject_missing_boundary_when_limit_is_erased(self):
        self.data["obligations"][0]["limitation"] = " "
        with self.assertRaisesRegex(ValueError, "missing boundary"):
            GATE.validate_ledger(self.data)

    def test_should_reject_missing_model_when_artifact_is_stale(self):
        row = next(r for r in self.data["obligations"] if r["status"] == "kernel-model")
        row["artifact"] = "Libp2p/Missing.lean#absent"
        with self.assertRaisesRegex(ValueError, "missing model artifact"):
            GATE.validate_ledger(self.data)

    def test_should_reject_missing_symbol_when_model_changes(self):
        row = next(r for r in self.data["obligations"] if r["status"] == "kernel-model")
        row["artifact"] = "Libp2p/Pipeline.lean#nonexistent_theorem"
        with self.assertRaisesRegex(ValueError, "missing model symbol"):
            GATE.validate_ledger(self.data)

    def test_should_reject_stale_count_when_metadata_disagrees(self):
        self.data["inventory_children"] = 159
        with self.assertRaisesRegex(ValueError, "metadata is stale"):
            GATE.validate_ledger(self.data)

    def test_should_reject_escaped_path_when_artifact_leaves_models(self):
        row = next(r for r in self.data["obligations"] if r["status"] == "kernel-model")
        row["artifact"] = "../outside.lean#irrelevant"
        with self.assertRaisesRegex(ValueError, "escapes the model directory"):
            GATE.validate_ledger(self.data)

    def test_should_reject_duplicate_inventory_id_when_source_is_inconsistent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            properties = root / "docs/properties"
            properties.mkdir(parents=True)
            (properties / "one.md").write_text("| A-01.01 | a |\n| A-01.01 | b |\n")
            with self.assertRaisesRegex(ValueError, "duplicate child IDs"):
                GATE.inventory_ids(root)


if __name__ == "__main__":
    unittest.main()
