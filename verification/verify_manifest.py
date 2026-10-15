#!/usr/bin/env python3
"""Validate exact mathematical sources, compiled declarations, and kernel evidence."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import gzip
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PARTIAL_HELPER = "MatrixTransport.ReactionZero.SelectorApproximation.finiteSelector._unsafe_rec"
PINS = {
    "lean_toolchain": "leanprover/lean4:v4.34.0-rc2",
    "lean_commit": "6a10ac8c22beadecabdbb0919c2b50214762f91d",
    "mathlib_commit": "71a80585ee495fc24472fd0eaffc89d94e4fd8d6",
    "exporter_commit": "483e011449cce37c3f8ad5e2aae434cbb1d2e53c",
    "nanoda_commit": "3a2407216ee84a75f9e1aead6803d0578be06ae7",
}
KINDS = {"theorem", "definition", "opaque", "inductive", "constructor", "recursor", "quotient"}
CONTROLS = (
    "source-hashes.json", "compiled-declarations.json", "exclusions.json", "targets.txt",
    "modules.txt", "verify_manifest.py", "check-kernels.sh", "tests/test_verify_manifest.py",
    "ATOMIC_INVENTORY.json", "PARAGRAPH_MAP.json", "ATOM_MAP.json", "STATEMENT_MAP.md",
    "declaration-types.json.gz", "DumpTypes.lean", "check_atom_map.py", "tests/test_check_atom_map.py",
    "resource-control.sh", "tests/test_resource_control.py",
)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def lines(path: Path) -> list[str]:
    rows = path.read_text().splitlines()
    if not rows or any(not row or row != row.strip() for row in rows) or len(set(rows)) != len(rows):
        raise ValueError(f"Empty, repeated, or whitespace-padded entries in {path.name}")
    return rows


def source_files(formal: Path) -> set[str]:
    result = {
        str(path.relative_to(formal)) for path in formal.rglob("*.lean")
        if ".lake" not in path.relative_to(formal).parts
        and ".git" not in path.relative_to(formal).parts
    }
    result.update({"lean-toolchain", "lakefile.lean", "lake-manifest.json"})
    return result


def check_sources(formal: Path, manifest: dict[str, str]) -> None:
    actual = source_files(formal)
    if set(manifest) != actual:
        raise ValueError(f"Source inventory mismatch: missing={sorted(actual-set(manifest))}, "
                         f"extra={sorted(set(manifest)-actual)}")
    for name, expected in manifest.items():
        path = formal / name
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(formal.resolve()):
            raise ValueError(f"Nonlocal or missing proof source: {name}")
        if not re.fullmatch(r"[0-9a-f]{64}", expected) or digest(path) != expected:
            raise ValueError(f"Source hash mismatch: {name}")
    if (formal / "lean-toolchain").read_text().strip() != PINS["lean_toolchain"]:
        raise ValueError("Unexpected Lean toolchain")
    mathlib = [p for p in read_json(formal / "lake-manifest.json")["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != PINS["mathlib_commit"]:
        raise ValueError("Unexpected mathlib revision")


def validate_inventory(payload: dict, targets: list[str], exclusions: list[dict]) -> dict[str, str]:
    if payload.get("schema_version") != 1 or not isinstance(payload.get("declarations"), list):
        raise ValueError("Unsupported compiled declaration inventory")
    rows = payload["declarations"]
    names = [row["name"] for row in rows]
    if not rows or names != sorted(set(names)):
        raise ValueError("Compiled declarations must be nonempty, unique, and sorted")
    if len(exclusions) != 1:
        raise ValueError("Exactly the documented compiler partial helper must be excluded")
    exception = exclusions[0]
    expected = {"name": PARTIAL_HELPER, "kind": "definition", "unsafe": False, "partial": True}
    if (any(exception.get(key) != value for key, value in expected.items())
            or type(exception.get("unsafe")) is not bool
            or type(exception.get("partial")) is not bool
            or not isinstance(exception.get("reason"), str) or not exception["reason"].strip()):
        raise ValueError("Invalid compiler-helper exception")
    selected = {}
    found_exception = False
    for row in rows:
        if not isinstance(row.get("axioms"), list) or not set(row["axioms"]) <= ALLOWED_AXIOMS:
            raise ValueError(f"Nonstandard or absent axiom audit: {row['name']}")
        if type(row.get("unsafe")) is not bool or type(row.get("partial")) is not bool:
            raise ValueError(f"Invalid safety flags: {row['name']}")
        if row["name"] == PARTIAL_HELPER:
            if any(row.get(key) != value for key, value in expected.items()):
                raise ValueError("Compiler-helper signature changed")
            found_exception = True
            continue
        if row["kind"] not in KINDS or row["unsafe"] or row["partial"]:
            raise ValueError(f"Unsafe, partial, or project axiom declaration: {row['name']}")
        selected[row["name"]] = row["kind"]
    if not found_exception:
        raise ValueError("Documented compiler helper absent from the compiled inventory")
    if targets != sorted(selected):
        raise ValueError("Targets must cover exactly every safe compiled project declaration")
    return selected


def collector_payload(text: str) -> dict:
    begin, end = "MANUSCRIPT_DECLARATIONS_BEGIN", "MANUSCRIPT_DECLARATIONS_END"
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError("Missing or repeated declaration collector markers")
    middle = text.split(begin, 1)[1].split(end, 1)[0].strip()
    return json.loads(middle)


def verify_nanoda_log(text: str, kinds: dict[str, str]) -> dict:
    summaries = re.findall(r"^Checked (\d+) declarations with no errors$", text, re.M)
    if len(summaries) != 1 or int(summaries[0]) < len(kinds):
        raise ValueError("Missing complete successful Nanoda closure summary")
    headers = re.findall(r"^(theorem|def|opaque|inductive|constructor|recursor|quotient|axiom) (\S+)", text, re.M)
    printed = [(name.split(".{", 1)[0], kind) for kind, name in headers if kind != "axiom"]
    expected = {name: "def" if kind == "definition" else kind for name, kind in kinds.items()}
    if len(printed) != len(kinds) or len(dict(printed)) != len(printed) or dict(printed) != expected:
        raise ValueError("Nanoda printed target signatures/categories do not match the manifest")
    axioms = [name.split(".{", 1)[0] for kind, name in headers if kind == "axiom"]
    if len(axioms) != len(ALLOWED_AXIOMS) or set(axioms) != ALLOWED_AXIOMS:
        raise ValueError("Nanoda reported an unexpected axiom set")
    return {"checked_declarations": int(summaries[0]), "permitted_axioms": sorted(axioms),
            "selected_kind_counts": dict(Counter(kinds.values()))}


def checkpoint(root: Path, formal: Path) -> dict:
    directory = root / "verification"
    sources = read_json(directory / "source-hashes.json")
    check_sources(formal, sources)
    validate_inventory(read_json(directory / "compiled-declarations.json"),
                       lines(directory / "targets.txt"), read_json(directory / "exclusions.json"))
    if lines(directory / "modules.txt") != ["MatrixTransport", "MatrixTransport.Paper"]:
        raise ValueError("Unexpected aggregate module list")
    controls = {name: digest(directory / name) for name in CONTROLS}
    controls[".github/workflows/verify.yml"] = digest(root / ".github/workflows/verify.yml")
    return {"source_hashes": sources, "control_hashes": controls}


def git_commit(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def require_committed_sources(root: Path, formal: Path, sources: dict[str, str]) -> None:
    if not formal.is_relative_to(root):
        raise ValueError("The proof tree must be inside the repository")
    relative = formal.relative_to(root)
    paths = [str(relative / name) for name in sources]
    paths += [str(Path("verification") / name) for name in CONTROLS]
    paths.append(".github/workflows/verify.yml")
    tracked = set(subprocess.check_output(
        ["git", "-C", str(root), "ls-files", "--", *paths], text=True).splitlines())
    if tracked != set(paths):
        raise ValueError("Proof sources and verification controls must all be tracked")
    if subprocess.run(["git", "-C", str(root), "diff", "--quiet", "HEAD", "--", *paths]).returncode:
        raise ValueError("Verified sources differ from the recorded repository commit")


def check_type_log_integrity(output: Path) -> dict:
    packed = output / "types-trust0.log.gz"
    expected = (output / "types-trust0-raw-SHA256SUMS").read_text().strip().split()
    if len(expected) != 2 or expected[1] != "types-trust0.log" or not re.fullmatch(r"[0-9a-f]{64}", expected[0]):
        raise ValueError("Invalid complete type-log integrity record")
    hasher, byte_count = hashlib.sha256(), 0
    with gzip.open(packed, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(chunk)
            byte_count += len(chunk)
    if hasher.hexdigest() != expected[0] or str(byte_count) != (output / "types-trust0-raw-bytes.txt").read_text().strip():
        raise ValueError("Complete fresh type-log restoration differs from its integrity record")
    return {"raw_sha256": expected[0], "raw_bytes": byte_count, "gzip_sha256": digest(packed)}


def check_statement_correspondence(root: Path, formal: Path, output: Path) -> dict:
    directory = root / "verification"
    spec = importlib.util.spec_from_file_location("statement_map_checker", directory / "check_atom_map.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    result = module.validate(root, formal,
        module.read_json(directory / "ATOMIC_INVENTORY.json"),
        module.read_json(directory / "PARAGRAPH_MAP.json"),
        module.read_json(directory / "ATOM_MAP.json"),
        module.read_json(directory / "declaration-types.json.gz"),
        lines(directory / "targets.txt"), {"mathlib": formal / ".lake/packages/mathlib"},
        module.read_type_dump(output / "types-trust0.log.gz"),
        module.read_json(directory / "compiled-declarations.json"))
    if read_json(output / "atomic-correspondence-check.log") != result:
        raise ValueError("Recorded statement-map summary differs from the final current-source check")
    return result


def certificate(root: Path, formal: Path, output: Path, exporter: Path, checker: Path) -> dict:
    before, after = read_json(output / "checkpoint-before.json"), checkpoint(root, formal)
    if before != after:
        raise ValueError("Proof sources or verification controls changed during kernel verification")
    require_committed_sources(root, formal, after["source_hashes"])
    kinds = validate_inventory(read_json(root / "verification/compiled-declarations.json"),
                               lines(root / "verification/targets.txt"),
                               read_json(root / "verification/exclusions.json"))
    if collector_payload((output / "lean-trust0.log").read_text()) != read_json(
            root / "verification/compiled-declarations.json"):
        raise ValueError("The trust=0 collector differs from the committed inventory")
    for stage in ("lake-build", "lean-trust0", "types-trust0", "atom-map", "export", "nanoda"):
        if (output / f"{stage}-exit.txt").read_text().strip() != "0":
            raise ValueError(f"Missing successful verification step: {stage}")
    config = read_json(output / "nanoda-config.json")
    if config != nanoda_config(output, lines(root / "verification/targets.txt")):
        raise ValueError("Nanoda configuration differs from the required kernel boundaries")
    if git_commit(exporter) != PINS["exporter_commit"] or git_commit(checker) != PINS["nanoda_commit"]:
        raise ValueError("Proof tool revision mismatch")
    verified = verify_nanoda_log((output / "nanoda-check.log").read_text(), kinds)
    type_log = check_type_log_integrity(output)
    statement_map = check_statement_correspondence(root, formal, output)
    result = {
        "schema_version": 1, "status": "PASS", "tool_pins": PINS,
        "scope": "Every selected safe compiled project declaration and its full dependency closure",
        "lean_trust_level": 0, "selected_declarations": sorted(kinds),
        "excluded_declarations": read_json(root / "verification/exclusions.json"),
        "nanoda": verified, "repository_commit": git_commit(root), **after,
        "fresh_declaration_types": type_log, "recorded_statement_map": statement_map,
        "export_sha256": digest(output / "export.ndjson"),
        "export_bytes": (output / "export.ndjson").stat().st_size,
        "nanoda_binary_sha256": digest(checker / "target/release/nanoda_bin"),
        "nanoda_Cargo_lock_sha256": digest(checker / "Cargo.lock"),
        "exporter_binary_sha256": digest(exporter / ".lake/build/bin/lean4export"),
        "config_sha256": digest(output / "nanoda-config.json"),
        "verification_environment": "github-actions" if os.environ.get("GITHUB_ACTIONS") == "true" else "local",
    }
    if os.environ.get("GITHUB_ACTIONS") == "true":
        result["github_run_url"] = (f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/"
                                    f"{os.environ['GITHUB_RUN_ID']}")
    return result


def nanoda_config(output: Path, targets: list[str]) -> dict:
    return {"export_file_path": str((output / "export.ndjson").resolve()),
            "permitted_axioms": sorted(ALLOWED_AXIOMS), "unpermitted_axiom_hard_error": True,
            "unsafe_permit_all_axioms": False, "num_threads": 2, "nat_extension": True,
            "string_extension": True, "print_success_message": True, "print_axioms": True,
            "pp_to_stdout": True, "unknown_pp_declar_hard_error": True, "pp_declars": targets}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--formal-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--mode", choices=("check", "collector", "config", "certificate"), default="check")
    parser.add_argument("--log", type=Path)
    parser.add_argument("--exporter-dir", type=Path)
    parser.add_argument("--checker-dir", type=Path)
    args = parser.parse_args()
    root, formal = args.root.resolve(), args.formal_dir.resolve()
    if args.mode == "check":
        result = checkpoint(root, formal)
        if args.output:
            write_json(args.output, result)
    elif args.mode == "collector":
        result = collector_payload(args.log.read_text())
        if result != read_json(root / "verification/compiled-declarations.json"):
            raise ValueError("Compiled declaration inventory differs from the manifest")
        validate_inventory(result, lines(root / "verification/targets.txt"),
                           read_json(root / "verification/exclusions.json"))
    elif args.mode == "config":
        result = nanoda_config(args.output, lines(root / "verification/targets.txt"))
        write_json(args.output / "nanoda-config.json", result)
    else:
        result = certificate(root, formal, args.output, args.exporter_dir, args.checker_dir)
        write_json(args.output / "certificate.json", result)
    print(json.dumps({"mode": args.mode, "status": "PASS"}))


if __name__ == "__main__":
    main()
