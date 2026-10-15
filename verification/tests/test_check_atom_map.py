"""Regression tests for source and kernel-type bindings in the atomic statement map."""
from copy import deepcopy
import gzip
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("check_atom_map", Path(__file__).parents[1] / "check_atom_map.py")
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class AtomicMapTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.formal = self.root / "formal"
        source = self.formal / "MatrixTransport/Example.lean"
        source.parent.mkdir(parents=True)
        source.write_text("namespace MatrixTransport\ntheorem Example : True := trivial\nend MatrixTransport\n")
        manuscript = self.root / "manuscript"
        (manuscript / "figures").mkdir(parents=True)
        original = Path(__file__).parents[2] / next(iter(checker.FIGURES))
        shutil.copyfile(original, self.root / next(iter(checker.FIGURES)))
        main = manuscript / "main.tex"
        lines = [f"Paragraph {i}.\n" for i in range(checker.PARAGRAPH_COUNT - 1)] + [checker.AI_TEXT + "\n"]
        main.write_text("".join(lines))
        (manuscript / "references.bib").write_text("@article{Ref, doi = {10.1234/example}, title={Example}}\n")
        (self.root / "numerical").mkdir()
        (self.root / "numerical/results.csv").write_text("case,value\na,0.1234\n")
        self.inventory = {"schema_version": 1, "atoms": []}
        self.map = {"schema_version": 1, "atoms": [], "sources": {},
                    "baseline": {"ai_text": checker.AI_TEXT, "figures": deepcopy(checker.FIGURES)},
                    "bibliography": [{"key": "Ref", "locator": "https://doi.org/10.1234/example"}]}
        declaration = {"name": "MatrixTransport.Example", "origin": "project", "kind": "theorem",
                       "module": "MatrixTransport.Example", "type_repr": "Lean.Expr.const `True []",
                       "type_pretty": "True", "source_file": "MatrixTransport/Example.lean",
                       "source_sha256": checker.digest(source), "unsafe": False, "partial": False,
                       "axioms": []}
        declaration["type_sha256"] = checker.type_digest(declaration["type_repr"])
        self.registry = {"schema_version": 1, "declarations": [declaration]}
        self.live_dump = deepcopy(self.registry)
        self.compiled = deepcopy(self.registry)
        self.targets = [declaration["name"]]
        for i in range(checker.ATOM_COUNT):
            category = ["mathematical", "literature", "numerical"][i] if i < 3 else "nonmathematical"
            atom_id = f"A{i:03d}"
            atom = {"id": atom_id, "claim": f"Claim {i}", "category": category,
                    "locations": [{"file": "manuscript/main.tex", "start_line": i % checker.PARAGRAPH_COUNT + 1,
                                   "end_line": i % checker.PARAGRAPH_COUNT + 1}],
                    "requires_substitutions": i == 0, "requires_assumptions": i == 0}
            self.inventory["atoms"].append(atom)
            row = {"id": atom_id, "claim": atom["claim"], "category": category, "status": "complete",
                   "mappings": [], "substitutions": [], "assumptions": [], "evidence": [],
                   "source_locations": deepcopy(atom["locations"]), "dependencies_on_atoms": []}
            if i == 0:
                row["mappings"] = [{key: declaration[key] for key in
                                    ("name", "type_sha256", "source_file", "source_sha256")}]
                row["mappings"][0].update(local_proposition="True", context="Unit-test declaration context")
                row["substitutions"] = ["No free variables"]
                row["assumptions"] = ["No additional hypotheses"]
            elif i == 1:
                row["evidence"] = [{"kind": "citation", "key": "Ref", "locator": "https://doi.org/10.1234/example"}]
            elif i == 2:
                row["evidence"] = [{"kind": "csv_value", "file": "numerical/results.csv",
                                    "sha256": checker.digest(self.root / "numerical/results.csv"),
                                    "where": {"case": "a"}, "column": "value", "value": "0.123", "decimal_places": 3}]
            self.map["atoms"].append(row)
        self.paragraphs = {"schema_version": 1, "paragraphs": [], "auxiliary_tex": []}
        for i, line in enumerate(lines):
            self.paragraphs["paragraphs"].append({"id": f"P{i:02d}", "file": "manuscript/main.tex",
                "start_line": i + 1, "end_line": i + 1, "text_sha256": checker.type_digest(line),
                "atom_ids": [f"A{j:03d}" for j in range(checker.ATOM_COUNT) if j % checker.PARAGRAPH_COUNT == i]})
        self.refresh_sources()

    def refresh_sources(self):
        self.map["sources"] = {str(p.relative_to(self.root)): checker.digest(p)
                               for p in self.root.rglob("*") if p.is_file() and not p.is_relative_to(self.formal)}

    def validate(self):
        return checker.validate(self.root, self.formal, self.inventory, self.paragraphs,
                                self.map, self.registry, self.targets, live_dump=self.live_dump,
                                compiled=self.compiled)

    def test_complete_inventory_and_rounded_value_pass(self):
        self.assertEqual(self.validate()["atoms"], checker.ATOM_COUNT)

    def run_checker(self, *arguments):
        directory = self.root / "verification"
        directory.mkdir(exist_ok=True)
        for name, value in (("ATOMIC_INVENTORY.json", self.inventory),
                            ("PARAGRAPH_MAP.json", self.paragraphs),
                            ("ATOM_MAP.json", self.map),
                            ("declaration-types.json", self.registry)):
            (directory / name).write_text(json.dumps(value))
        (directory / "targets.txt").write_text("\n".join(self.targets) + "\n")
        return subprocess.run([sys.executable, str(Path(checker.__file__)),
                               "--root", str(self.root), *arguments],
                              capture_output=True, text=True)

    def test_source_only_cli_identifies_its_limited_scope(self):
        result = self.run_checker("--source-bindings-only")
        self.assertEqual(result.returncode, 0, result.stderr)
        summary = json.loads(result.stdout)
        self.assertEqual(summary["atoms"], checker.ATOM_COUNT)
        self.assertEqual(summary["validation_scope"], "source-and-stored-declaration-bindings")
        self.assertIs(summary["fresh_type_dump_checked"], False)
        self.assertIs(summary["kernel_rerun"], False)

    def test_source_only_cli_still_rejects_source_drift(self):
        (self.root / "manuscript/main.tex").write_text("Changed source\n")
        result = self.run_checker("--source-bindings-only")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Source hash mismatch", result.stderr)

    def test_source_only_cli_still_rejects_stored_type_digest_drift(self):
        self.registry["declarations"][0]["type_repr"] = "Lean.Expr.const `False []"
        result = self.run_checker("--source-bindings-only")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Declaration type hash mismatch", result.stderr)

    def test_cli_requires_an_explicit_validation_mode(self):
        result = self.run_checker()
        self.assertEqual(result.returncode, 2)
        self.assertIn("is required", result.stderr)

    def test_source_only_cli_cannot_be_combined_with_a_fresh_dump(self):
        result = self.run_checker("--source-bindings-only", "--raw-types", "unused.json")
        self.assertEqual(result.returncode, 2)
        self.assertIn("not allowed", result.stderr)

    def test_retired_editorial_atom_cannot_replace_an_active_atom_at_same_count(self):
        for retired_id in sorted(checker.RETIRED_EDITORIAL_ATOM_IDS):
            with self.subTest(retired_id=retired_id):
                original_id = self.inventory["atoms"][-1]["id"]
                self.inventory["atoms"][-1]["id"] = retired_id
                self.map["atoms"][-1]["id"] = retired_id
                for paragraph in self.paragraphs["paragraphs"]:
                    paragraph["atom_ids"] = [retired_id if atom_id == original_id else atom_id
                                             for atom_id in paragraph["atom_ids"]]
                with self.assertRaisesRegex(ValueError, "Retired editorial atoms"):
                    self.validate()
                self.inventory["atoms"][-1]["id"] = original_id
                self.map["atoms"][-1]["id"] = original_id
                for paragraph in self.paragraphs["paragraphs"]:
                    paragraph["atom_ids"] = [original_id if atom_id == retired_id else atom_id
                                             for atom_id in paragraph["atom_ids"]]

    def relocate_first_paragraph_without_changing_mathematical_payload(self):
        main = self.root / "manuscript/main.tex"
        lines = main.read_text().splitlines(keepends=True)
        moved = self.root / "manuscript/sections/tools.tex"
        moved.parent.mkdir()
        moved.write_text(lines[0])
        lines[0] = "\n"
        main.write_text("".join(lines))
        self.paragraphs["paragraphs"][0]["file"] = "manuscript/sections/tools.tex"
        ids = set(self.paragraphs["paragraphs"][0]["atom_ids"])
        for atom, row in zip(self.inventory["atoms"], self.map["atoms"]):
            if atom["id"] in ids:
                atom["locations"][0]["file"] = "manuscript/sections/tools.tex"
                row["source_locations"] = deepcopy(atom["locations"])
        self.refresh_sources()

    def test_verbatim_paragraph_relocation_keeps_math_payload_and_strict_coverage(self):
        keys = ("id", "claim", "mappings", "substitutions", "assumptions", "dependencies_on_atoms")
        before = [{key: deepcopy(row[key]) for key in keys} for row in self.map["atoms"]
                  if row["category"] == "mathematical"]
        self.relocate_first_paragraph_without_changing_mathematical_payload()
        after = [{key: deepcopy(row[key]) for key in keys} for row in self.map["atoms"]
                 if row["category"] == "mathematical"]
        self.assertEqual(before, after)
        self.assertEqual(self.validate()["paragraphs"], checker.PARAGRAPH_COUNT)
        self.assertEqual(self.validate()["atoms"], checker.ATOM_COUNT)

    def test_relocated_paragraph_with_stale_atom_anchor_is_rejected(self):
        self.relocate_first_paragraph_without_changing_mathematical_payload()
        self.inventory["atoms"][0]["locations"][0]["file"] = "manuscript/main.tex"
        self.map["atoms"][0]["source_locations"] = deepcopy(self.inventory["atoms"][0]["locations"])
        with self.assertRaisesRegex(ValueError, "no source intersection"):
            self.validate()

    def test_missing_row_rejected(self):
        self.map["atoms"].pop()
        with self.assertRaisesRegex(ValueError, "missing or extra"):
            self.validate()

    def test_expanded_proof_detail_needs_an_actual_type_even_with_source_evidence(self):
        self.inventory["atoms"][-1]["category"] = "mathematical"
        row = self.map["atoms"][-1]
        row["category"] = "mathematical"
        row["evidence"] = [{"kind": "file", "file": "numerical/results.csv",
                            "sha256": checker.digest(self.root / "numerical/results.csv"),
                            "description": "A recorded file cannot replace a mathematical realization"}]
        with self.assertRaisesRegex(ValueError, "Mathematical row lacks actual types"):
            self.validate()

    def test_expanded_proof_detail_must_record_its_own_instantiation_context(self):
        self.inventory["atoms"][-1]["category"] = "mathematical"
        row = self.map["atoms"][-1]
        row["category"] = "mathematical"
        row["mappings"] = deepcopy(self.map["atoms"][0]["mappings"])
        row["mappings"][0]["context"] = ""
        with self.assertRaisesRegex(ValueError, "Missing mapping context"):
            self.validate()

    def test_extra_row_rejected(self):
        row = deepcopy(self.map["atoms"][-1]); row["id"] = "EXTRA"
        self.map["atoms"].append(row)
        with self.assertRaisesRegex(ValueError, "missing or extra"):
            self.validate()

    def test_duplicate_row_rejected(self):
        self.map["atoms"].append(deepcopy(self.map["atoms"][-1]))
        with self.assertRaisesRegex(ValueError, "Duplicate map ID"):
            self.validate()

    def test_source_drift_rejected(self):
        (self.root / "manuscript/main.tex").write_text("Changed source\n")
        with self.assertRaisesRegex(ValueError, "Source hash mismatch"):
            self.validate()

    def test_malformed_source_array_rejected(self):
        self.map["sources"] = [{"file": "manuscript/main.tex"}]
        with self.assertRaisesRegex(ValueError, "Sources must be a hash object"):
            self.validate()

    def test_duplicate_compiled_target_rejected(self):
        self.targets.append(self.targets[0])
        with self.assertRaisesRegex(ValueError, "Duplicate compiled target"):
            self.validate()

    def test_formal_source_drift_rejected(self):
        (self.formal / "MatrixTransport/Example.lean").write_text("axiom changed : False\n")
        with self.assertRaisesRegex(ValueError, "Source hash mismatch"):
            self.validate()

    def test_type_repr_drift_rejected(self):
        self.registry["declarations"][0]["type_repr"] = "Lean.Expr.const `False []"
        with self.assertRaisesRegex(ValueError, "Live declaration type_repr mismatch"):
            self.validate()

    def test_forged_self_consistent_type_rejected_against_live_dump(self):
        row = self.registry["declarations"][0]
        row["type_repr"] = "Lean.Expr.const `False []"
        row["type_sha256"] = checker.type_digest(row["type_repr"])
        self.map["atoms"][0]["mappings"][0]["type_sha256"] = row["type_sha256"]
        with self.assertRaisesRegex(ValueError, "Live declaration type_repr mismatch"):
            self.validate()

    def test_false_axiom_metadata_rejected(self):
        self.registry["declarations"][0]["axioms"] = ["propext"]
        with self.assertRaisesRegex(ValueError, "Live declaration axioms mismatch"):
            self.validate()

    def test_false_kind_metadata_rejected(self):
        self.registry["declarations"][0]["kind"] = "definition"
        with self.assertRaisesRegex(ValueError, "Live declaration kind mismatch"):
            self.validate()

    def test_false_safety_flag_rejected(self):
        self.registry["declarations"][0]["unsafe"] = True
        with self.assertRaisesRegex(ValueError, "Live declaration unsafe mismatch"):
            self.validate()

    def test_compiled_kind_mismatch_rejected(self):
        self.compiled["declarations"][0]["kind"] = "definition"
        with self.assertRaisesRegex(ValueError, "Compiled declaration kind mismatch"):
            self.validate()

    def test_absent_live_dump_rejected(self):
        self.live_dump = None
        with self.assertRaisesRegex(ValueError, "live type dump schema"):
            self.validate()

    def test_mapping_type_hash_mismatch_rejected(self):
        self.map["atoms"][0]["mappings"][0]["type_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Mapping type_sha256 mismatch"):
            self.validate()

    def test_unresolved_row_rejected(self):
        self.map["atoms"][0]["status"] = "pending"
        with self.assertRaisesRegex(ValueError, "Unresolved atomic"):
            self.validate()

    def test_reclassified_mathematical_claim_rejected(self):
        self.map["atoms"][0]["category"] = "nonmathematical"
        with self.assertRaisesRegex(ValueError, "category changed"):
            self.validate()

    def test_empty_context_rejected(self):
        self.map["atoms"][0]["mappings"][0]["context"] = ""
        with self.assertRaisesRegex(ValueError, "Missing mapping context"):
            self.validate()

    def test_missing_required_substitution_rejected(self):
        self.map["atoms"][0]["substitutions"] = []
        with self.assertRaisesRegex(ValueError, "Missing substitutions"):
            self.validate()

    def test_nonempty_line_coverage_hole_rejected(self):
        path = self.root / "manuscript/main.tex"
        path.write_text(path.read_text() + "Unmapped mathematics.\n")
        self.refresh_sources()
        with self.assertRaisesRegex(ValueError, "no paragraph coverage"):
            self.validate()

    def test_missing_atomic_location_rejected(self):
        self.inventory["atoms"][0]["locations"] = []
        self.map["atoms"][0]["source_locations"] = []
        with self.assertRaisesRegex(ValueError, "Missing atomic location"):
            self.validate()

    def test_unknown_atomic_dependency_rejected(self):
        self.map["atoms"][0]["dependencies_on_atoms"] = ["MISSING"]
        with self.assertRaisesRegex(ValueError, "Unknown atomic dependency"):
            self.validate()

    def test_duplicate_atomic_dependency_rejected(self):
        self.map["atoms"][0]["dependencies_on_atoms"] = ["A001", "A001"]
        with self.assertRaisesRegex(ValueError, "Duplicate atomic dependency"):
            self.validate()

    def test_self_referential_atomic_dependency_rejected(self):
        self.map["atoms"][0]["dependencies_on_atoms"] = ["A000"]
        with self.assertRaisesRegex(ValueError, "Self-referential atomic dependency"):
            self.validate()

    def test_valid_atomic_dependency_passes(self):
        self.map["atoms"][0]["dependencies_on_atoms"] = ["A001"]
        self.assertEqual(self.validate()["atoms"], checker.ATOM_COUNT)

    def test_mapped_source_location_mismatch_rejected(self):
        self.map["atoms"][0]["source_locations"][0]["start_line"] = 2
        with self.assertRaisesRegex(ValueError, "source_locations differ"):
            self.validate()

    def test_wrong_paragraph_association_rejected(self):
        self.inventory["atoms"][0]["locations"][0].update(start_line=2, end_line=2)
        self.map["atoms"][0]["source_locations"] = deepcopy(self.inventory["atoms"][0]["locations"])
        with self.assertRaisesRegex(ValueError, "association has no source intersection"):
            self.validate()

    def test_broad_source_range_does_not_require_all_paragraph_memberships(self):
        self.inventory["atoms"][0]["locations"][0]["end_line"] = checker.PARAGRAPH_COUNT
        self.map["atoms"][0]["source_locations"] = deepcopy(self.inventory["atoms"][0]["locations"])
        self.assertEqual(self.validate()["atoms"], checker.ATOM_COUNT)

    def test_overlapping_paragraphs_rejected(self):
        row = self.paragraphs["paragraphs"][1]
        row.update(start_line=1, end_line=1, text_sha256=self.paragraphs["paragraphs"][0]["text_sha256"])
        with self.assertRaisesRegex(ValueError, "Overlapping paragraph"):
            self.validate()

    def test_paragraph_hash_drift_rejected(self):
        self.paragraphs["paragraphs"][0]["text_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Paragraph hash mismatch"):
            self.validate()

    def test_false_empirical_value_rejected(self):
        self.map["atoms"][2]["evidence"][0]["value"] = "0.124"
        with self.assertRaisesRegex(ValueError, "False empirical value"):
            self.validate()

    def test_nonunique_csv_selector_rejected(self):
        path = self.root / "numerical/results.csv"
        path.write_text(path.read_text() + "a,0.1234\n")
        self.refresh_sources()
        self.map["atoms"][2]["evidence"][0]["sha256"] = checker.digest(path)
        with self.assertRaisesRegex(ValueError, "CSV selector is not unique"):
            self.validate()

    def test_changed_ai_even_with_updated_source_hash_rejected(self):
        path = self.root / "manuscript/main.tex"
        path.write_text(path.read_text().replace("takes full responsibility", "delegates responsibility"))
        self.refresh_sources()
        with self.assertRaisesRegex(ValueError, "AI declaration was changed"):
            self.validate()

    def test_changed_ai_baseline_rejected(self):
        self.map["baseline"]["ai_text"] += " Extra statement."
        with self.assertRaisesRegex(ValueError, "AI baseline was changed"):
            self.validate()

    def test_changed_figure_baseline_rejected(self):
        self.map["baseline"]["figures"][next(iter(checker.FIGURES))] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Figure baseline was changed"):
            self.validate()

    def test_standard_boolean_alone_is_not_evidence(self):
        source = self.root / "standard/Mathlib/Extra.lean"
        source.parent.mkdir(parents=True); source.write_text("theorem standard : True := trivial\n")
        row = deepcopy(self.registry["declarations"][0])
        row.update(name="Some.standard", origin="standard", module="Mathlib.Extra",
                   source_root="mathlib", source_file="Mathlib/Extra.lean",
                   source_sha256=checker.digest(source), checked_dependency=True)
        self.registry["declarations"].append(row)
        self.live_dump["declarations"].append(deepcopy(row))
        with self.assertRaisesRegex(ValueError, "Missing source path"):
            checker.validate(self.root, self.formal, self.inventory, self.paragraphs,
                             self.map, self.registry, self.targets, {"mathlib": self.root / "standard"},
                             self.live_dump, self.compiled)

    def test_duplicate_json_keys_rejected(self):
        path = self.root / "duplicate.json"; path.write_text('{"sources":{},"sources":[]}')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            checker.read_json(path)

    def test_gzip_json_and_dump_boundaries(self):
        path = self.root / "types.json.gz"
        with gzip.open(path, "wt") as stream:
            json.dump(self.registry, stream)
        self.assertEqual(checker.read_json(path), self.registry)
        log = "DECLARATION_TYPES_BEGIN\n" + json.dumps(self.registry) + "\nDECLARATION_TYPES_END"
        self.assertEqual(checker.parse_type_dump(log), self.registry)
        with self.assertRaises(ValueError):
            checker.parse_type_dump(log + "\nDECLARATION_TYPES_BEGIN")


if __name__ == "__main__":
    unittest.main()
