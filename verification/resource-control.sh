#!/usr/bin/env bash
# Resource controls change scheduling only; all proof and kernel checks remain mandatory.
resource_snapshot() {
  local label=$1
  {
    printf '\nUTC=%s phase=%s\n' "$(date -u +%FT%TZ)" "$label"
    free -m
    df -Pk "$output_dir"
    for record in memory.current memory.max memory.events; do
      if [[ -r /sys/fs/cgroup/$record ]]; then
        printf 'cgroup_%s=' "$record"
        tr '\n' ' ' < "/sys/fs/cgroup/$record"
        printf '\n'
      fi
    done
    # Process listings are diagnostics; unavailable ps must not stop proof checks.
    if ! ps -eo pid,ppid,rss,comm --sort=-rss 2>&1 | awk 'NR <= 16'; then
      printf 'process_diagnostics=unavailable\n'
    fi
  } >> "$output_dir/resource-samples.log"
  printf '[verification] UTC=%s phase=%s MemAvailable_kB=%s disk_available_kB=%s\n' \
    "$(date -u +%FT%TZ)" "$label" \
    "$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)" \
    "$(df -Pk "$output_dir" | awk 'NR == 2 {print $4}')"
}

resource_phase() {
  resource_current_phase=$1
  printf '%s\n' "$resource_current_phase" > "$output_dir/current-phase.txt"
  printf '%s %s\n' "$(date -u +%FT%TZ)" "$resource_current_phase" >> "$output_dir/phases.log"
  resource_snapshot "$resource_current_phase"
}

resource_is_hosted() {
  [[ ${GITHUB_ACTIONS:-} == true && ${RUNNER_ENVIRONMENT:-} == github-hosted ]]
}

resource_require_disk() {
  local label=$1 minimum_kib=$2 available_kib
  available_kib=$(df -Pk "$output_dir" | awk 'NR == 2 {print $4}')
  if [[ ! $available_kib =~ ^[0-9]+$ ]] || (( available_kib < minimum_kib )); then
    printf 'Insufficient disk reserve for %s: available=%s KiB, required=%s KiB\n' \
      "$label" "$available_kib" "$minimum_kib" >&2
    return 1
  fi
  printf '%s phase=%s available_kib=%s minimum_kib=%s\n' \
    "$(date -u +%FT%TZ)" "$label" "$available_kib" "$minimum_kib" \
    >> "$output_dir/disk-reserve-checks.log"
}

resource_prepare_download_cache() {
  if resource_is_hosted; then
    resource_require_disk pre-cache 14680064
    resource_mathlib_cache=$(mktemp -d "${TMPDIR:-/tmp}/matrix-transport-mathlib-cache.XXXXXX")
    export MATHLIB_CACHE_DIR=$resource_mathlib_cache
  fi
}

resource_release_download_cache() {
  if resource_is_hosted && [[ -n ${resource_mathlib_cache:-} ]]; then
    resource_phase mathlib-download-cache-release
    du -sk "$resource_mathlib_cache" >> "$output_dir/released-build-caches.log"
    rm -rf -- "$resource_mathlib_cache"
  fi
}

resource_release_checker_intermediates() {
  if resource_is_hosted; then
    local binary=$checker_dir/target/release/nanoda_bin before after entry
    before=$(sha256sum "$binary" | cut -d ' ' -f 1)
    resource_phase checker-intermediate-release
    # Preserve the exact executable and all checked tool source/lock files.
    for entry in deps build .fingerprint incremental examples; do
      if [[ -d $checker_dir/target/release/$entry ]]; then
        du -sk "$checker_dir/target/release/$entry" >> "$output_dir/released-build-caches.log"
        rm -rf -- "$checker_dir/target/release/$entry"
      fi
    done
    after=$(sha256sum "$binary" | cut -d ' ' -f 1)
    test "$before" = "$after"
    printf '%s  nanoda_bin (retained before/after intermediate release)\n' "$after" \
      >> "$output_dir/released-build-caches.log"
  fi
}

resource_control_init() {
  command -v flock > /dev/null
  local real_sysroot entry
  real_sysroot=$(lean --print-prefix)
  export PROOF_REAL_LEAN=$real_sysroot/bin/lean
  test "$("$PROOF_REAL_LEAN" --githash)" = 6a10ac8c22beadecabdbb0919c2b50214762f91d
  resource_toolchain=$(mktemp -d "${TMPDIR:-/tmp}/matrix-transport-toolchain.XXXXXX")
  mkdir "$resource_toolchain/bin"
  for entry in "$real_sysroot"/*; do
    if [[ ${entry##*/} != bin ]]; then
      ln -s "$entry" "$resource_toolchain/${entry##*/}"
    fi
  done
  for entry in "$real_sysroot/bin"/*; do
    if [[ ${entry##*/} != lean ]]; then
      ln -s "$entry" "$resource_toolchain/bin/${entry##*/}"
    fi
  done
  export PROOF_LEAN_LOCK=$resource_toolchain/lean-process.lock
  export PROOF_LEAN_PROCESS_LOG=$output_dir/lean-processes.log
  cat > "$resource_toolchain/bin/lean" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
# Lake's supported sysroot override retains this compiler path.
# flock propagates the real compiler's status and leaves every argument intact.
printf -v invocation '%q ' "$PROOF_REAL_LEAN" --threads=1 "$@"
printf 'UTC=%s wrapper_pid=%s requested_argv=%s\n' "$(date -u +%FT%TZ)" "$$" "$invocation" \
  >> "$PROOF_LEAN_PROCESS_LOG"
exec flock --exclusive "$PROOF_LEAN_LOCK" "$PROOF_REAL_LEAN" --threads=1 "$@"
WRAPPER
  chmod 755 "$resource_toolchain/bin/lean"
  cp "$resource_toolchain/bin/lean" "$output_dir/lean-process-wrapper.txt"
  {
    printf 'max_concurrent_lean_processes=1\nlean_threads_per_process=1\n'
    printf 'real_toolchain_sysroot=%s\n' "$real_sysroot"
    sha256sum "$PROOF_REAL_LEAN"
  } > "$output_dir/resource-policy.txt"
  export LEAN_SYSROOT=$resource_toolchain
  export LAKE_OVERRIDE_LEAN=true
  resource_phase initialization
  (
    trap 'kill "${monitor_sleep_pid:-}" 2>/dev/null || true; exit 0' TERM INT
    while true; do
      sleep 30 &
      monitor_sleep_pid=$!
      wait "$monitor_sleep_pid" || exit 0
      resource_snapshot "$(cat "$output_dir/current-phase.txt")"
    done
  ) &
  resource_monitor_pid=$!
}

resource_control_cleanup() {
  local status=$1
  if [[ -n ${resource_monitor_pid:-} ]]; then
    kill "$resource_monitor_pid" 2>/dev/null || true
    wait "$resource_monitor_pid" 2>/dev/null || true
  fi
  resource_snapshot "exit:$status" || true
  if ! printf '%s\n' "$status" > "$output_dir/pipeline-exit.txt"; then
    printf 'Could not retain exit-status diagnostic; original pipeline status=%s\n' "$status" >&2
  fi
  if [[ -n ${resource_mathlib_cache:-} ]]; then
    rm -rf -- "$resource_mathlib_cache"
  fi
  if [[ -n ${resource_toolchain:-} ]]; then
    rm -rf -- "$resource_toolchain"
  fi
}
