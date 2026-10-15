#!/usr/bin/env bash
# Build the mathematical package and independently verify the exact declaration closure.
set -euo pipefail
project_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
formal_dir=${PROOF_FORMAL_DIR:-$project_root/formal/weight_limits}
if [[ ! -d "$formal_dir" && -d "$project_root/formal" ]]; then
  formal_dir=$project_root/formal
fi
formal_dir=$(cd "$formal_dir" && pwd)
exporter_dir=${PROOF_EXPORTER_DIR:-$project_root/.proof-tools/exporter}
checker_dir=${PROOF_NANODA_DIR:-$project_root/.proof-tools/checker}
output_dir=${PROOF_OUTPUT_DIR:-$project_root/.verification}
mkdir -p "$output_dir"
output_dir=$(cd "$output_dir" && pwd)
if [[ -n "$(find "$output_dir" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  echo 'Use an empty verification output directory to preserve previous evidence.' >&2
  exit 2
fi
source "$project_root/verification/resource-control.sh"
trap 'resource_control_cleanup "$?"' EXIT
resource_control_init
exporter_dir=$(cd "$exporter_dir" && pwd)
checker_dir=$(cd "$checker_dir" && pwd)
check_tools() {
  test "$(git -C "$exporter_dir" rev-parse HEAD)" = 483e011449cce37c3f8ad5e2aae434cbb1d2e53c
  test "$(git -C "$checker_dir" rev-parse HEAD)" = 3a2407216ee84a75f9e1aead6803d0578be06ae7
  test -z "$(git -C "$exporter_dir" status --porcelain --untracked-files=normal)"
  test -z "$(git -C "$checker_dir" status --porcelain --untracked-files=normal)"
  test "$(cat "$exporter_dir/lean-toolchain")" = leanprover/lean4:v4.34.0-rc2
}
resource_phase source-and-tool-check
check_tools
resource_prepare_download_cache
verify=(python3 "$project_root/verification/verify_manifest.py" --root "$project_root" --formal-dir "$formal_dir")
"${verify[@]}" --mode check --output "$output_dir/checkpoint-before.json" > "$output_dir/source-check-before.log"
cp "$project_root"/verification/{modules.txt,targets.txt,compiled-declarations.json,source-hashes.json,exclusions.json} "$output_dir/"
cp "$formal_dir/lake-manifest.json" "$output_dir/lake-manifest.json"
git -C "$project_root" rev-parse HEAD > "$output_dir/repository-commit.txt"
rustc --version > "$output_dir/rust-version.txt"
cargo --version > "$output_dir/cargo-version.txt"
(
  cd "$formal_dir"
  test ! -e .lake/package-overrides.json
  test "$(lake env lean --githash)" = 6a10ac8c22beadecabdbb0919c2b50214762f91d
  lake env lean --version > "$output_dir/lean-version.txt"
  resource_phase mathlib-cache
  lake exe cache get 2>&1 | tee "$output_dir/mathlib-cache.log"
  test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = 71a80585ee495fc24472fd0eaffc89d94e4fd8d6
  resource_release_download_cache
  resource_phase formal-build
  lake build MatrixTransport MatrixTransport.Paper 2>&1 | tee "$output_dir/lake-build.log"
)
printf '0\n' > "$output_dir/lake-build-exit.txt"
resource_phase trust-zero-collector
(
  cd "$formal_dir"
  lake env lean --trust=0 -DautoImplicit=false CollectManuscriptTargets.lean 2>&1 | tee "$output_dir/lean-trust0.log"
)
printf '0\n' > "$output_dir/lean-trust0-exit.txt"
resource_phase collector-comparison
"${verify[@]}" --mode collector --log "$output_dir/lean-trust0.log" > "$output_dir/compiled-coverage-check.log"
(
  cd "$formal_dir"
  resource_phase trust-zero-type-dump
  if resource_is_hosted; then resource_require_disk fresh-types 2097152; fi
  lake env lean --trust=0 -DautoImplicit=false "$project_root/verification/DumpTypes.lean" \
    > "$output_dir/types-trust0.log" 2>&1
)
printf '0\n' > "$output_dir/types-trust0-exit.txt"
resource_phase type-log-compression
# Keep the complete fresh kernel types without a large uncompressed artifact.
types_raw_sha=$(sha256sum "$output_dir/types-trust0.log" | cut -d ' ' -f 1)
types_raw_bytes=$(wc -c < "$output_dir/types-trust0.log")
gzip -n -c "$output_dir/types-trust0.log" > "$output_dir/types-trust0.log.gz"
gzip -t "$output_dir/types-trust0.log.gz"
test "$types_raw_sha" = "$(gzip -cd "$output_dir/types-trust0.log.gz" | sha256sum | cut -d ' ' -f 1)"
printf '%s  types-trust0.log\n' "$types_raw_sha" > "$output_dir/types-trust0-raw-SHA256SUMS"
printf '%s\n' "$types_raw_bytes" > "$output_dir/types-trust0-raw-bytes.txt"
rm -- "$output_dir/types-trust0.log"
resource_phase atomic-correspondence
python3 "$project_root/verification/check_atom_map.py" --root "$project_root" \
  --formal-root "$formal_dir" --mathlib-root "$formal_dir/.lake/packages/mathlib" \
  --type-dump-log "$output_dir/types-trust0.log.gz" > "$output_dir/atomic-correspondence-check.log"
printf '0\n' > "$output_dir/atom-map-exit.txt"
(
  cd "$exporter_dir"
  resource_phase exporter-build
  lake build 2>&1 | tee "$output_dir/exporter-build.log"
)
(
  cd "$checker_dir"
  resource_phase nanoda-build
  cargo build --release --locked 2>&1 | tee "$output_dir/nanoda-build.log"
)
resource_release_checker_intermediates
cp "$checker_dir/Cargo.lock" "$output_dir/nanoda-Cargo.lock"
mapfile -t modules < "$project_root/verification/modules.txt"
mapfile -t targets < "$project_root/verification/targets.txt"
(
  cd "$formal_dir"
  resource_phase declaration-export
  if resource_is_hosted; then resource_require_disk complete-export 2097152; fi
  lake env "$exporter_dir/.lake/build/bin/lean4export" "${modules[@]}" -- "${targets[@]}" \
    > "$output_dir/export.ndjson" 2> "$output_dir/export.log"
)
printf '0\n' > "$output_dir/export-exit.txt"
"${verify[@]}" --mode config --output "$output_dir" > "$output_dir/config-generation.log"
resource_phase nanoda-closure
"$checker_dir/target/release/nanoda_bin" "$output_dir/nanoda-config.json" 2>&1 | tee "$output_dir/nanoda-check.log"
printf '0\n' > "$output_dir/nanoda-exit.txt"
resource_phase final-source-and-certificate
"${verify[@]}" --mode check --output "$output_dir/checkpoint-after.json" > "$output_dir/source-check-after.log"
check_tools
"${verify[@]}" --mode certificate --output "$output_dir" --exporter-dir "$exporter_dir" \
  --checker-dir "$checker_dir" > "$output_dir/certificate-generation.log"
# All kernel checks and the source/tool checkpoints are complete. On an ephemeral
# Actions runner, release rebuildable caches before retaining a second export copy.
# Keep local caches and every verification artifact intact.
if resource_is_hosted; then
  df -h "$output_dir"
  rm -rf -- "$formal_dir/.lake" "$exporter_dir/.lake" "$checker_dir/target"
  df -h "$output_dir"
fi
resource_phase export-compression
gzip -n -c "$output_dir/export.ndjson" > "$output_dir/export.ndjson.gz"
gzip -t "$output_dir/export.ndjson.gz"
resource_phase complete
# Finalize diagnostics before hashing; the EXIT handler must not mutate checksummed logs.
resource_control_cleanup 0
trap - EXIT
(
  cd "$output_dir"
  find . -maxdepth 1 -type f ! -name export.ndjson ! -name artifact-SHA256SUMS -print0 \
    | sort -z | xargs -0 sha256sum > artifact-SHA256SUMS
)
