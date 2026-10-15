"""Failure-path tests for the mathematical verification boundary."""
from copy import deepcopy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import subprocess
import unittest

SPEC = importlib.util.spec_from_file_location("verify_manifest", Path(__file__).parents[1] / "verify_manifest.py")
verification = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verification)


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.rows = [
            {"name": "MatrixTransport.Constructor", "kind": "constructor", "axioms": [], "unsafe": False, "partial": False},
            {"name": verification.PARTIAL_HELPER, "kind": "definition", "axioms": [], "unsafe": False, "partial": True},
            {"name": "MatrixTransport.theorem", "kind": "theorem", "axioms": ["propext"], "unsafe": False, "partial": False},
        ]
        self.payload = {"schema_version": 1, "declarations": self.rows}
        self.targets = ["MatrixTransport.Constructor", "MatrixTransport.theorem"]
        self.exceptions = [dict(self.rows[1], reason="Compiler-generated partial implementation helper")]

    def validate(self):
        return verification.validate_inventory(self.payload, self.targets, self.exceptions)

    def test_valid_inventory_retains_structural_declarations(self):
        self.assertEqual(self.validate()["MatrixTransport.Constructor"], "constructor")

    def test_missing_structural_target_rejected(self):
        self.targets.pop(0)
        with self.assertRaises(ValueError):
            self.validate()

    def test_unsafe_declaration_rejected(self):
        self.rows[2]["unsafe"] = True
        with self.assertRaises(ValueError):
            self.validate()

    def test_other_partial_declaration_rejected(self):
        self.rows[2]["partial"] = True
        with self.assertRaises(ValueError):
            self.validate()

    def test_nonstandard_axiom_rejected(self):
        self.rows[2]["axioms"] = ["sorryAx"]
        with self.assertRaises(ValueError):
            self.validate()

    def test_project_axiom_rejected(self):
        self.rows[2]["kind"] = "axiom"
        with self.assertRaises(ValueError):
            self.validate()

    def test_partial_exception_cannot_cover_unsafe_code(self):
        self.rows[1]["unsafe"] = True
        with self.assertRaises(ValueError):
            self.validate()

    def test_exception_cannot_be_renamed(self):
        self.exceptions[0]["name"] = "MatrixTransport.anotherHelper"
        with self.assertRaises(ValueError):
            self.validate()

    def test_duplicate_compiled_row_rejected(self):
        self.rows.append(deepcopy(self.rows[-1]))
        with self.assertRaises(ValueError):
            self.validate()

    def test_collector_payload_boundaries(self):
        log = "MANUSCRIPT_DECLARATIONS_BEGIN\n" + json.dumps(self.payload) + "\nMANUSCRIPT_DECLARATIONS_END"
        self.assertEqual(verification.collector_payload(log), self.payload)
        with self.assertRaises(ValueError):
            verification.collector_payload(log + "\nMANUSCRIPT_DECLARATIONS_BEGIN")


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.formal = Path(self.temporary.name)
        (self.formal / "Main.lean").write_text("theorem actual : True := trivial\n")
        (self.formal / "lakefile.lean").write_text("import Lake\n")
        (self.formal / "lean-toolchain").write_text(verification.PINS["lean_toolchain"] + "\n")
        (self.formal / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "mathlib", "rev": verification.PINS["mathlib_commit"]}]}))
        self.manifest = {name: verification.digest(self.formal / name)
                         for name in verification.source_files(self.formal)}

    def validate(self):
        verification.check_sources(self.formal, self.manifest)

    def test_valid_sources(self):
        self.validate()

    def test_modified_source_rejected(self):
        (self.formal / "Main.lean").write_text("axiom actual : False\n")
        with self.assertRaises(ValueError):
            self.validate()

    def test_unrecorded_source_rejected(self):
        (self.formal / "Extra.lean").write_text("axiom injected : False\n")
        with self.assertRaises(ValueError):
            self.validate()

    def test_removed_source_rejected(self):
        (self.formal / "Main.lean").unlink()
        with self.assertRaises(ValueError):
            self.validate()

    def test_source_symlink_rejected_even_if_hash_matches(self):
        target = self.formal / "Original.txt"
        target.write_bytes((self.formal / "Main.lean").read_bytes())
        (self.formal / "Main.lean").unlink()
        (self.formal / "Main.lean").symlink_to(target)
        with self.assertRaises(ValueError):
            self.validate()

    def test_dependency_cache_sources_not_project_sources(self):
        (self.formal / ".lake").mkdir()
        (self.formal / ".lake/External.lean").write_text("external cache\n")
        self.validate()

    def test_toolchain_change_rejected_even_with_recomputed_hash(self):
        (self.formal / "lean-toolchain").write_text("leanprover/lean4:nightly\n")
        self.manifest["lean-toolchain"] = verification.digest(self.formal / "lean-toolchain")
        with self.assertRaises(ValueError):
            self.validate()


class CommitTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.formal = self.root / "formal"
        self.formal.mkdir()
        (self.formal / "Main.lean").write_text("theorem actual : True := trivial\n")
        self.sources = {"Main.lean": verification.digest(self.formal / "Main.lean")}
        (self.root / "verification").mkdir()
        for name in verification.CONTROLS:
            path = self.root / "verification" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("verification control\n")
        workflow = self.root / ".github/workflows/verify.yml"
        workflow.parent.mkdir(parents=True)
        workflow.write_text("workflow\n")
        self.git("init", "-q")
        self.git("add", "formal/Main.lean", "verification", ".github/workflows/verify.yml")
        self.git("-c", "user.name=Verification Test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "Test fixture")

    def git(self, *args):
        subprocess.run(["git", "-C", str(self.root), *args], check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def validate(self):
        verification.require_committed_sources(self.root, self.formal, self.sources)

    def test_committed_sources_match_recorded_commit(self):
        self.validate()

    def test_uncommitted_proof_change_rejected(self):
        (self.formal / "Main.lean").write_text("axiom changed : False\n")
        with self.assertRaises(ValueError):
            self.validate()

    def test_staged_proof_change_rejected(self):
        (self.formal / "Main.lean").write_text("axiom changed : False\n")
        self.git("add", "formal/Main.lean")
        with self.assertRaises(ValueError):
            self.validate()

    def test_uncommitted_statement_map_change_rejected(self):
        (self.root / "verification/ATOM_MAP.json").write_text('{"changed": true}\n')
        with self.assertRaises(ValueError):
            self.validate()

    def test_untracked_source_cannot_be_certified(self):
        (self.formal / "New.lean").write_text("theorem newFact : True := trivial\n")
        self.sources["New.lean"] = verification.digest(self.formal / "New.lean")
        with self.assertRaises(ValueError):
            self.validate()


class TypeLogIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.output = Path(self.temporary.name)
        self.raw = b'DECLARATION_TYPES_BEGIN\n{"schema_version":1}\nDECLARATION_TYPES_END\n'
        with gzip.open(self.output / "types-trust0.log.gz", "wb") as stream:
            stream.write(self.raw)
        checksum = hashlib.sha256(self.raw).hexdigest()
        (self.output / "types-trust0-raw-SHA256SUMS").write_text(checksum + "  types-trust0.log\n")
        (self.output / "types-trust0-raw-bytes.txt").write_text(str(len(self.raw)) + "\n")

    def test_lossless_type_log_integrity_passes(self):
        record = verification.check_type_log_integrity(self.output)
        self.assertEqual(record["raw_bytes"], len(self.raw))
        self.assertEqual(record["raw_sha256"], hashlib.sha256(self.raw).hexdigest())

    def test_changed_raw_type_digest_rejected(self):
        (self.output / "types-trust0-raw-SHA256SUMS").write_text("0" * 64 + "  types-trust0.log\n")
        with self.assertRaisesRegex(ValueError, "restoration differs"):
            verification.check_type_log_integrity(self.output)

    def test_changed_type_byte_count_rejected(self):
        (self.output / "types-trust0-raw-bytes.txt").write_text(str(len(self.raw) - 1) + "\n")
        with self.assertRaisesRegex(ValueError, "restoration differs"):
            verification.check_type_log_integrity(self.output)

    def test_wrong_type_log_identity_rejected(self):
        (self.output / "types-trust0-raw-SHA256SUMS").write_text(hashlib.sha256(self.raw).hexdigest() + "  other.log\n")
        with self.assertRaisesRegex(ValueError, "Invalid complete type-log"):
            verification.check_type_log_integrity(self.output)


class NanodaTests(unittest.TestCase):
    def setUp(self):
        self.kinds = {"MatrixTransport.theorem": "theorem", "MatrixTransport.definition": "definition"}
        self.log = ("theorem MatrixTransport.theorem : True := _\n"
                    "def MatrixTransport.definition : Nat := 0\n"
                    "axiom propext : _\naxiom Classical.choice.{u} : _\naxiom Quot.sound.{u} : _\n"
                    "Checked 100 declarations with no errors\n")

    def test_complete_closure_and_exact_targets(self):
        self.assertEqual(verification.verify_nanoda_log(self.log, self.kinds)["checked_declarations"], 100)

    def test_missing_signature_rejected(self):
        with self.assertRaises(ValueError):
            verification.verify_nanoda_log(self.log.replace("def MatrixTransport.definition : Nat := 0\n", ""), self.kinds)

    def test_duplicate_signature_rejected(self):
        with self.assertRaises(ValueError):
            verification.verify_nanoda_log(self.log + "theorem MatrixTransport.theorem : True := _\n", self.kinds)

    def test_unknown_target_rejected(self):
        with self.assertRaises(ValueError):
            verification.verify_nanoda_log(self.log.replace("MatrixTransport.theorem", "MatrixTransport.other"), self.kinds)

    def test_missing_success_summary_rejected(self):
        with self.assertRaises(ValueError):
            verification.verify_nanoda_log(self.log.replace("Checked 100 declarations with no errors", "Failed"), self.kinds)

    def test_unexpected_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verification.verify_nanoda_log(self.log.replace("axiom propext", "axiom sorryAx"), self.kinds)

    def test_unknown_targets_and_nonstandard_axioms_are_hard_errors(self):
        config = verification.nanoda_config(Path("/tmp/kernel-output"), list(self.kinds))
        self.assertTrue(config["unknown_pp_declar_hard_error"])
        self.assertTrue(config["unpermitted_axiom_hard_error"])
        self.assertFalse(config["unsafe_permit_all_axioms"])
        self.assertEqual(set(config["permitted_axioms"]), verification.ALLOWED_AXIOMS)


if __name__ == "__main__":
    unittest.main()
