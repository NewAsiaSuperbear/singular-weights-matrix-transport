#!/usr/bin/env python3
"""Check the source, declaration-type, and documentary bindings of the statement map.

This checks recorded correspondence data; semantic correspondence is reviewed separately.
Type digests are SHA256 of the exact UTF-8 kernel-expression representation from DumpTypes.
Paragraph digests use exact source lines, including their original line endings.
"""
import argparse
import csv
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
import hashlib
import gzip
import json
from pathlib import Path
import re

ATOM_COUNT = 797
RETIRED_EDITORIAL_ATOM_IDS = frozenset({"NU09", "VE05", "LA26", "EX12"})
PARAGRAPH_COUNT = 79
CATEGORIES = {"mathematical", "literature", "numerical", "nonmathematical"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AI_TEXT = ("Generative AI tools contributed to the mathematical development and the organization and revision "
           "of this manuscript. The author provided initial ideas, made substantive contributions to refining "
           "the results, reviewed the arguments, and takes full responsibility for the final content.")
FIGURES = {"manuscript/figures/theory_comparisons.pdf":
           "ba76166d4c19b04cd06450451cc6e4c76059e4482755ac6dcb0232755d48bdbc"}
AUXILIARY_TEX = {"manuscript/citation-links.tex"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def type_digest(text):
    require(isinstance(text, str) and bool(text.strip()), "Empty declaration type")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    path = Path(path)
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            return json.load(stream, object_pairs_hook=unique_object)
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)


def parse_type_dump(text):
    begin, end = "DECLARATION_TYPES_BEGIN", "DECLARATION_TYPES_END"
    require(text.count(begin) == 1 and text.count(end) == 1, "Invalid type-dump boundaries")
    middle = text.split(begin, 1)[1].split(end, 1)[0].strip()
    return json.loads(middle, object_pairs_hook=unique_object)


def read_type_dump(path):
    path = Path(path)
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            return parse_type_dump(stream.read())
    return parse_type_dump(path.read_text(encoding="utf-8"))


def declaration_table(payload, label):
    require(isinstance(payload, dict) and payload.get("schema_version") == 1,
            f"Missing or unsupported {label} schema")
    require(isinstance(payload.get("declarations"), list), f"{label} declarations must be an array")
    result = {}
    for row in payload["declarations"]:
        require(isinstance(row, dict), f"Malformed {label} declaration")
        name = row.get("name")
        require(isinstance(name, str) and bool(name), f"Unnamed {label} declaration")
        require(name not in result, f"Duplicate {label} declaration: {name}")
        result[name] = row
    return result


def validate_live_types(registry, live_dump, compiled, targets):
    live = declaration_table(live_dump, "live type dump")
    compiled_rows = declaration_table(compiled, "compiled inventory")
    require({name for name in live if project_name(name)} == targets,
            "Live type dump differs from compiled project targets")
    safe_compiled = {name for name, row in compiled_rows.items()
                     if project_name(name) and row.get("unsafe") is False and row.get("partial") is False}
    require(safe_compiled == targets, "Compiled inventory differs from project targets")
    keys = ("name", "origin", "module", "kind", "type_repr", "type_pretty", "unsafe", "partial")
    for row in registry.get("declarations", []):
        name = row.get("name")
        require(name in live, f"Stored declaration absent from live dump: {name}")
        for key in keys:
            require(row.get(key) == live[name].get(key), f"Live declaration {key} mismatch: {name}")
        require(sorted(row.get("axioms", [])) == sorted(live[name].get("axioms", [])),
                f"Live declaration axioms mismatch: {name}")
        if project_name(name):
            require(name in compiled_rows, f"Declaration absent from compiled inventory: {name}")
            for key in ("kind", "unsafe", "partial"):
                require(row.get(key) == compiled_rows[name].get(key), f"Compiled declaration {key} mismatch: {name}")
            require(sorted(row.get("axioms", [])) == sorted(compiled_rows[name].get("axioms", [])),
                    f"Compiled declaration axioms mismatch: {name}")


def relative_file(root, name):
    require(isinstance(name, str) and bool(name), "Missing source path")
    path = Path(name)
    require(not path.is_absolute() and ".." not in path.parts, f"Invalid relative path: {name}")
    resolved = (root / path).resolve()
    require(resolved.is_relative_to(root.resolve()), f"Source path escapes root: {name}")
    require(resolved.is_file(), f"Missing source file: {name}")
    return resolved


def checked_file(root, name, expected):
    path = relative_file(root, name)
    require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
            f"Invalid source hash: {name}")
    require(digest(path) == expected, f"Source hash mismatch: {name}")
    return path


def indexed(rows, label):
    require(isinstance(rows, list), f"{label} must be an array")
    result = {}
    for row in rows:
        require(isinstance(row, dict), f"Malformed {label} row")
        key = row.get("id")
        require(isinstance(key, str) and bool(key), f"Missing {label} ID")
        require(key not in result, f"Duplicate {label} ID: {key}")
        result[key] = row
    return result


def nonempty_strings(values, label, required=False):
    require(isinstance(values, list), f"{label} must be an array")
    require(all(isinstance(v, str) and bool(v.strip()) for v in values), f"Empty {label} entry")
    require(not required or bool(values), f"Missing {label}")


def project_name(name):
    return name.startswith(("MatrixTransport.", "LiZouTransport.", "_private.MatrixTransport."))


def location_intersects(unit, location):
    return (unit["file"] == location["file"] and
            max(unit["start_line"], location["start_line"]) <=
            min(unit["end_line"], location["end_line"]))


def validate_registry(root, formal, registry, targets, standard_roots):
    require(registry.get("schema_version") == 1, "Unsupported declaration schema")
    rows = registry.get("declarations")
    require(isinstance(rows, list), "Declarations must be an array")
    by_name = {}
    standard_names = []
    for row in rows:
        name = row.get("name")
        require(isinstance(name, str) and bool(name), "Missing declaration name")
        require(name not in by_name, f"Duplicate declaration name: {name}")
        require(row.get("type_sha256") == type_digest(row.get("type_repr")),
                f"Declaration type hash mismatch: {name}")
        require(isinstance(row.get("type_pretty"), str) and bool(row["type_pretty"].strip()),
                f"Missing readable declaration type: {name}")
        require(row.get("unsafe") is False and row.get("partial") is False,
                f"Unsafe or partial declaration: {name}")
        require(set(row.get("axioms", [])) <= AXIOMS, f"Unpermitted declaration axiom: {name}")
        origin = row.get("origin")
        require(origin in {"project", "standard"}, f"Invalid declaration origin: {name}")
        require((origin == "project") == project_name(name), f"False declaration origin: {name}")
        require(row.get("kind") in {"theorem", "definition", "opaque", "axiom", "inductive",
                                    "constructor", "recursor", "quotient"}, "Invalid declaration kind")
        require(not (origin == "project" and row["kind"] == "axiom"), "Project axioms are forbidden")
        source = row.get("source_file")
        if origin == "project":
            require(name in targets, f"Project declaration outside compiled targets: {name}")
            checked_file(formal, source, row.get("source_sha256"))
        else:
            standard_names.append(name)
            source_root = row.get("source_root")
            require(source_root in standard_roots, f"Missing standard source root: {name}")
            checked_file(standard_roots[source_root], source, row.get("source_sha256"))
            require(row.get("checked_dependency") is True, f"Unchecked standard declaration: {name}")
        require(row.get("module") == str(Path(source).with_suffix("")).replace("/", "."),
                f"Declaration source/module mismatch: {name}")
        by_name[name] = row
    require({n for n, r in by_name.items() if r["origin"] == "project"} == targets,
            "Declaration types do not cover the complete compiled project target set")
    if standard_names:
        evidence = registry.get("standard_dependency_evidence", {})
        certificate = read_json(checked_file(root, evidence.get("certificate_file"),
                                             evidence.get("certificate_sha256")))
        require(certificate.get("export_sha256") == evidence.get("export_sha256") and
                bool(evidence.get("export_sha256")), "Standard declaration export is not bound")
        require(certificate.get("lean_trust_level") == 0, "Standard dependency certificate is not trust zero")
        require(set(certificate.get("nanoda", {}).get("permitted_axioms", [])) == AXIOMS,
                "Standard dependency certificate has a different axiom policy")
        closure_file = checked_file(root, evidence.get("declaration_names_file"),
                                    evidence.get("declaration_names_sha256"))
        closure = closure_file.read_text(encoding="utf-8").splitlines()
        require(len(closure) == len(set(closure)), "Duplicate dependency-closure names")
        require(all(name in closure for name in standard_names), "Standard declaration absent from checked closure")
        require(certificate.get("dependency_names_sha256") == evidence.get("declaration_names_sha256"),
                "Dependency-name list is not bound to the kernel certificate")
        require(isinstance(certificate.get("source_hashes"), dict), "Missing certified source hashes")
        for row in by_name.values():
            if row["origin"] == "project":
                require(certificate["source_hashes"].get(row["source_file"]) == row["source_sha256"],
                        "Standard dependency certificate is for different project sources")
    return by_name


def bibliography_entries(text):
    entries = {}
    starts = list(re.finditer(r"@\w+\s*\{\s*([^,\s]+)\s*,", text))
    for pos, match in enumerate(starts):
        stop = starts[pos + 1].start() if pos + 1 < len(starts) else len(text)
        key = match.group(1)
        require(key not in entries, f"Duplicate bibliography key: {key}")
        body = text[match.end():stop]
        fields = {}
        for field in ("doi", "url", "eprint", "isbn"):
            found = re.search(rf"\b{field}\s*=\s*(?:\{{([^}}]+)\}}|\"([^\"]+)\")", body, re.I)
            if found:
                fields[field] = (found.group(1) or found.group(2)).strip()
        entries[key] = fields
    return entries


def validate_evidence(root, row, bibliography, sources):
    evidence = row.get("evidence")
    require(isinstance(evidence, list), f"Missing evidence array: {row['id']}")
    require(row["category"] not in {"literature", "numerical"} or bool(evidence),
            f"Missing documentary evidence: {row['id']}")
    for item in evidence:
        kind = item.get("kind")
        if kind == "citation":
            key = item.get("key")
            require(key in bibliography and item.get("locator") == bibliography[key],
                    f"Citation locator mismatch: {row['id']}")
        elif kind in {"file", "csv_value"}:
            name = item.get("file")
            require(sources.get(name) == item.get("sha256"), f"Unbound evidence source: {row['id']}")
            path = checked_file(root, name, item.get("sha256"))
            if kind == "file":
                require(isinstance(item.get("description"), str) and bool(item["description"].strip()),
                        f"Missing evidence description: {row['id']}")
                continue
            require(path.suffix.lower() == ".csv", "Numeric value evidence must use CSV")
            where = item.get("where")
            require(isinstance(where, dict) and bool(where), "CSV row selector is empty")
            with path.open(encoding="utf-8", newline="") as stream:
                selected = [r for r in csv.DictReader(stream)
                            if all(r.get(k) == str(v) for k, v in where.items())]
            require(len(selected) == 1, f"CSV selector is not unique: {row['id']}")
            column = item.get("column")
            require(column in selected[0], f"CSV evidence column is absent: {row['id']}")
            places = item.get("decimal_places")
            require(isinstance(places, int) and not isinstance(places, bool) and 0 <= places <= 30,
                    "Invalid numerical precision")
            require(isinstance(item.get("value"), str), "Reported numeric value must be a decimal string")
            try:
                actual, reported = Decimal(selected[0][column]), Decimal(item["value"])
                require(actual.is_finite() and reported.is_finite(), "Nonfinite empirical value")
                quantum = Decimal(1).scaleb(-places)
                require(actual.quantize(quantum, rounding=ROUND_HALF_EVEN) == reported,
                        f"False empirical value: {row['id']}")
            except InvalidOperation as error:
                raise ValueError(f"Invalid empirical decimal: {row['id']}") from error
        else:
            raise ValueError(f"Unknown evidence kind: {kind}")
    if row["category"] == "literature":
        require(any(e.get("kind") == "citation" for e in evidence), "Literature row needs primary citation")
    if row["category"] == "numerical":
        require(any(e.get("kind") in {"file", "csv_value"} for e in evidence), "Numerical row needs recorded data")


def validate_recorded_bindings(root, formal, inventory, paragraphs, atom_map, registry, targets,
                               standard_roots=None):
    """Check current sources against recorded metadata, without fresh kernel evidence."""
    root, formal = Path(root), Path(formal)
    standard_roots = standard_roots or {}
    for obj, label in ((inventory, "inventory"), (paragraphs, "paragraphs"), (atom_map, "map")):
        require(obj.get("schema_version") == 1, f"Unsupported {label} schema")
    atoms = indexed(inventory.get("atoms"), "inventory")
    mapped = indexed(atom_map.get("atoms"), "map")
    require(len(atoms) == ATOM_COUNT, f"Inventory must contain exactly {ATOM_COUNT} atoms")
    require(not (set(atoms) & RETIRED_EDITORIAL_ATOM_IDS), "Retired editorial atoms cannot reappear in the active inventory")
    require(set(mapped) == set(atoms), "Atomic map has missing or extra IDs")
    for atom_id, row in mapped.items():
        require(row.get("source_locations") == atoms[atom_id].get("locations"),
                f"Mapped source_locations differ from inventory: {atom_id}")
        dependencies = row.get("dependencies_on_atoms")
        nonempty_strings(dependencies, f"dependencies_on_atoms for {atom_id}")
        require(len(dependencies) == len(set(dependencies)), f"Duplicate atomic dependency: {atom_id}")
        require(set(dependencies) <= set(atoms), f"Unknown atomic dependency: {atom_id}")
        require(atom_id not in dependencies, f"Self-referential atomic dependency: {atom_id}")
    sources = atom_map.get("sources")
    require(isinstance(sources, dict), "Sources must be a hash object")
    for name, expected in sources.items():
        checked_file(root, name, expected)
    baseline = atom_map.get("baseline", {})
    require(" ".join(str(baseline.get("ai_text", "")).split()) == AI_TEXT, "AI baseline was changed")
    require(baseline.get("figures") == FIGURES, "Figure baseline was changed")
    for name, expected in FIGURES.items():
        checked_file(root, name, expected)
    main = relative_file(root, "manuscript/main.tex").read_text(encoding="utf-8")
    disclosure = re.findall(r"Generative AI tools.*?final content\.", main, flags=re.S)
    require(len(disclosure) == 1 and " ".join(disclosure[0].split()) == AI_TEXT, "AI declaration was changed")
    units = indexed(paragraphs.get("paragraphs"), "paragraph")
    require(len(units) == PARAGRAPH_COUNT, f"Expected {PARAGRAPH_COUNT} paragraph units")
    auxiliary = paragraphs.get("auxiliary_tex", [])
    require(isinstance(auxiliary, list) and len(auxiliary) == len(set(auxiliary)) and
            set(auxiliary) <= AUXILIARY_TEX, "Invalid auxiliary TeX exclusion")
    tex_files = {str(p.relative_to(root)) for p in (root / "manuscript").rglob("*.tex")}
    require(all(name in tex_files for name in auxiliary), "Auxiliary TeX file is absent")
    require(tex_files <= set(sources), "Manuscript TeX source hash coverage is incomplete")
    for atom in atoms.values():
        locations = atom.get("locations")
        require(isinstance(locations, list) and bool(locations), f"Missing atomic location: {atom['id']}")
        for location in locations:
            name = location.get("file")
            require(name in tex_files - set(auxiliary), f"Invalid atomic source: {atom['id']}")
            count = len(relative_file(root, name).read_text(encoding="utf-8").splitlines())
            start, end = location.get("start_line"), location.get("end_line")
            require(type(start) is int and type(end) is int and 1 <= start <= end <= count,
                    f"Invalid atomic line range: {atom['id']}")
    line_sets, covered_atoms = {}, set()
    for unit in units.values():
        name = unit.get("file")
        require(name in tex_files - set(auxiliary), "Paragraph points outside exposition TeX")
        lines = relative_file(root, name).read_text(encoding="utf-8").splitlines(keepends=True)
        start, end = unit.get("start_line"), unit.get("end_line")
        require(type(start) is int and type(end) is int and 1 <= start <= end <= len(lines),
                f"Invalid paragraph range: {unit['id']}")
        text = "".join(lines[start - 1:end])
        require(type_digest(text) == unit.get("text_sha256"), f"Paragraph hash mismatch: {unit['id']}")
        coverage = set(range(start, end + 1))
        require(not (coverage & line_sets.get(name, set())), f"Overlapping paragraph coverage: {name}")
        line_sets.setdefault(name, set()).update(coverage)
        ids = unit.get("atom_ids")
        require(isinstance(ids, list) and bool(ids) and len(ids) == len(set(ids)), "Invalid paragraph atom IDs")
        require(set(ids) <= set(atoms), "Paragraph contains unknown atomic IDs")
        for atom_id in ids:
            require(any(location_intersects(unit, location) for location in atoms[atom_id]["locations"]),
                    f"Paragraph atomic association has no source intersection: {unit['id']} -> {atom_id}")
        covered_atoms.update(ids)
    require(covered_atoms == set(atoms), "Paragraph map omits atomic claims")
    for atom_id, atom in atoms.items():
        if atom["category"] == "mathematical":
            require(any(atom_id in unit["atom_ids"] and
                        any(location_intersects(unit, location) for location in atom["locations"])
                        for unit in units.values()), f"Mathematical atom has no source membership: {atom_id}")
    for name in tex_files - set(auxiliary):
        lines = relative_file(root, name).read_text(encoding="utf-8").splitlines()
        require(all(i in line_sets.get(name, set()) for i, text in enumerate(lines, 1) if text.strip()),
                f"Nonempty manuscript line has no paragraph coverage: {name}")
    target_names = list(targets)
    nonempty_strings(target_names, "compiled targets", required=True)
    require(len(target_names) == len(set(target_names)), "Duplicate compiled target")
    declarations = validate_registry(root, formal, registry, set(target_names), standard_roots)
    bib_path = "manuscript/references.bib"
    require(bib_path in sources, "Bibliography hash is absent")
    bib_entries = bibliography_entries(relative_file(root, bib_path).read_text(encoding="utf-8"))
    bibliography = {}
    require(isinstance(atom_map.get("bibliography"), list), "Bibliography locators must be an array")
    for item in atom_map["bibliography"]:
        key, locator = item.get("key"), item.get("locator")
        require(key in bib_entries and key not in bibliography, "Unknown or duplicate bibliography locator")
        fields = bib_entries[key]
        options = {fields.get("url"), fields.get("doi"), fields.get("isbn")}
        if fields.get("doi"):
            options.add("https://doi.org/" + fields["doi"])
        if fields.get("eprint"):
            options.add("https://arxiv.org/abs/" + fields["eprint"])
        require(isinstance(locator, str) and bool(locator) and locator in options,
                f"Primary bibliography locator differs from source: {key}")
        bibliography[key] = locator
    require(set(bibliography) == set(bib_entries), "Bibliography locator coverage is incomplete")
    for source in tex_files:
        text = relative_file(root, source).read_text(encoding="utf-8")
        for citation in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", text):
            require(all(k.strip() in bibliography for k in citation.split(",")), "Undefined citation key")
    for atom_id, row in mapped.items():
        reference = atoms[atom_id]
        category = row.get("category")
        require(category in CATEGORIES and category == reference.get("category"), f"Atomic category changed: {atom_id}")
        require(row.get("status") == "complete", f"Unresolved atomic row: {atom_id}")
        require(row.get("claim") == reference.get("claim") and bool(str(row.get("claim", "")).strip()),
                f"Atomic claim changed or empty: {atom_id}")
        nonempty_strings(row.get("substitutions"), f"substitutions for {atom_id}",
                         reference.get("requires_substitutions") is True)
        nonempty_strings(row.get("assumptions"), f"assumptions for {atom_id}",
                         reference.get("requires_assumptions") is True)
        mappings = row.get("mappings")
        require(isinstance(mappings, list), f"Mappings must be an array: {atom_id}")
        require(category != "mathematical" or bool(mappings), f"Mathematical row lacks actual types: {atom_id}")
        seen_names = set()
        for mapping in mappings:
            name = mapping.get("name")
            require(name in declarations and name not in seen_names, f"Unknown or duplicate mapping: {atom_id}")
            seen_names.add(name)
            declaration = declarations[name]
            for key in ("type_sha256", "source_file", "source_sha256"):
                require(mapping.get(key) == declaration.get(key), f"Mapping {key} mismatch: {atom_id}")
            for key in ("local_proposition", "context"):
                require(isinstance(mapping.get(key), str) and bool(mapping[key].strip()),
                        f"Missing mapping {key}: {atom_id}")
        validate_evidence(root, row, bibliography, sources)
    return {"atoms": len(atoms), "paragraphs": len(units), "declarations": len(declarations),
            "mathematical_atoms": sum(r["category"] == "mathematical" for r in mapped.values())}


def validate(root, formal, inventory, paragraphs, atom_map, registry, targets, standard_roots=None,
             live_dump=None, compiled=None):
    targets = list(targets)
    validate_live_types(registry, live_dump, compiled, set(targets))
    return validate_recorded_bindings(root, formal, inventory, paragraphs, atom_map, registry,
                                      targets, standard_roots)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--formal-root", type=Path)
    parser.add_argument("--mathlib-root", type=Path)
    parser.add_argument("--lean-root", type=Path)
    live = parser.add_mutually_exclusive_group(required=True)
    live.add_argument("--type-dump-log", type=Path, help="Fresh trust-zero DumpTypes output, optionally gzip")
    live.add_argument("--raw-types", type=Path, help="Parsed fresh DumpTypes JSON, optionally gzip")
    live.add_argument("--source-bindings-only", action="store_true",
                      help="Check source and stored declaration metadata only; no fresh kernel/type validation")
    args = parser.parse_args()
    root = args.root.resolve()
    formal = (args.formal_root or root / "formal").resolve()
    verification = root / "verification"
    type_path = verification / "declaration-types.json"
    if not type_path.exists():
        type_path = verification / "declaration-types.json.gz"
    standard_roots = {name: path.resolve() for name, path in
                      (("mathlib", args.mathlib_root), ("lean", args.lean_root)) if path}
    inputs = (root, formal, read_json(verification / "ATOMIC_INVENTORY.json"),
              read_json(verification / "PARAGRAPH_MAP.json"),
              read_json(verification / "ATOM_MAP.json"), read_json(type_path),
              (verification / "targets.txt").read_text(encoding="utf-8").splitlines(), standard_roots)
    if args.source_bindings_only:
        result = validate_recorded_bindings(*inputs)
        result.update(validation_scope="source-and-stored-declaration-bindings",
                      fresh_type_dump_checked=False, kernel_rerun=False)
    else:
        result = validate(*inputs,
                          read_type_dump(args.type_dump_log) if args.type_dump_log else read_json(args.raw_types),
                          read_json(verification / "compiled-declarations.json"))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
