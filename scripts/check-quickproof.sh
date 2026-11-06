#!/usr/bin/env bash
# Re-check the QuickProof theorems of experiments/quickproof/*/ (ADR 0030, issue #597).
#
# Optional, not part of the merge gate: QuickProof is under the PolyForm
# Noncommercial License and its toolchain includes CompCert (INRIA
# Non-Commercial License). This script runs the published Docker image; it
# needs docker and network access for the first pull.
#
# For each experiment it makes a QuickProof workspace whose upstream is this
# repository at the experiment's pinned commit. It runs `qp check` (lint, native
# ASan/UBSan runs, CompCert interpreter, mutants) when --check is given, then
# `qp assemble` (the frozen contract), copies the checked-in proof sources over
# the contract, commits them, and runs `qp verify`, which must print PASS.
#
# usage: scripts/check-quickproof.sh [--check] [EXPERIMENT...]
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image="${LEANOS_QUICKPROOF_IMAGE:-ghcr.io/genproof/quickproof@sha256:8d420bf40775d63aecf9475135e37167e1c1f96183617b853d9eac806aa6961a}"
check=0
if [[ "${1:-}" == "--check" ]]; then check=1; shift; fi
experiments=("$@")
if [[ ${#experiments[@]} -eq 0 ]]; then
  for d in "$root"/experiments/quickproof/*/; do experiments+=("$(basename "$d")"); done
fi
command -v docker >/dev/null || { echo "error: docker is required" >&2; exit 1; }
work="$(mktemp -d "${TMPDIR:-/tmp}/leanos-quickproof.XXXXXX")"
# A worktree's .git is a pointer into the main repository's: mount that too.
common="$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)"
extra=()
case "$common" in "$root"/*) ;; *) extra=(-v "$common:$common:ro") ;; esac
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/home" "$work/ws/projects"

qp() {  # run a shell command in the image, with this repository mounted read-only
  docker run --rm -i --user "$(id -u):$(id -g)" \
    -e HOME="$work/home" -e XDG_CACHE_HOME="$work/home/.cache" -e QP_CACHE="$work/home/.cache/quickproof" \
    -e QP_WORKSPACE="$work/ws" \
    -e GIT_AUTHOR_NAME=leanos -e GIT_AUTHOR_EMAIL=leanos@localhost \
    -e GIT_COMMITTER_NAME=leanos -e GIT_COMMITTER_EMAIL=leanos@localhost \
    -e GIT_CONFIG_COUNT=1 -e GIT_CONFIG_KEY_0=safe.directory -e GIT_CONFIG_VALUE_0='*' \
    -v "$work:$work" -v "$root:$root:ro" "${extra[@]}" -w "$work/ws" \
    --entrypoint /bin/bash "$image" -lc "$1"
}

for name in "${experiments[@]}"; do
  exp="$root/experiments/quickproof/$name"
  [[ -d "$exp/project" && -d "$exp/proof" ]] || { echo "error: $exp has no project/ and proof/" >&2; exit 1; }
  project="$work/ws/projects/${name//-/_}"
  cp -r "$exp/project" "$project"
  # The upstream is this repository; the pinned COMMIT in project.conf stays.
  sed -i "s|^UPSTREAM=.*|UPSTREAM=$root|" "$project/project.conf"
  pname="$(basename "$project")"
  if [[ "$check" -eq 1 ]]; then
    # An experiment whose laws run longer than the interpreter's default 10 s
    # per seed names its budget and qp check options in check.conf, which is
    # parsed here, not sourced.
    interp_timeout=10
    check_args=""
    if [[ -f "$exp/check.conf" ]]; then
      interp_timeout="$(sed -n 's/^GP_INTERP_TIMEOUT=\([0-9][0-9]*\)$/\1/p' "$exp/check.conf")"
      check_args="$(sed -n 's/^QP_CHECK_ARGS="\([-a-z0-9 ]*\)"$/\1/p' "$exp/check.conf")"
    fi
    # qp check reports in CHECK.md and exits 0 either way: keep the report and
    # judge it here. Every native and interpreter row must be ok, with no
    # interpreter seed timed out (a timed-out seed gives no verdict), the lint
    # clean, and the mutants killed no fewer than in the committed report.
    qp "GP_INTERP_TIMEOUT=${interp_timeout:-10} qp check $check_args $pname"
    out="$root/build/quickproof/$name"
    mkdir -p "$out"
    cp "$project/CHECK.md" "$out/CHECK.md"
    killed() { sed -n 's/^Killed by some harness: \*\*\([0-9]*\)\/.*/\1/p' "$1"; }
    bad="$(awk -F'|' '/^## Native runs/{s=1} /^## Mutants/{s=0} s && /^\| `/ && ($0 !~ /\| ok \(/ || $0 ~ /timed out/)' "$out/CHECK.md")"
    if [[ -n "$bad" ]]; then
      echo "error: $name: qp check found failures (see $out/CHECK.md):" >&2; echo "$bad" >&2; exit 1
    fi
    if ! awk '/^## VST lint/{s=1} s && /^clean$/{ok=1} END{exit !ok}' "$out/CHECK.md"; then
      echo "error: $name: the VST lint is not clean (see $out/CHECK.md)" >&2; exit 1
    fi
    now="$(killed "$out/CHECK.md")"; before="$(killed "$exp/CHECK.md")"
    if [[ -z "$now" || -z "$before" || "$now" -lt "$before" ]]; then
      echo "error: $name: ${now:-?} mutants killed, the committed CHECK.md has ${before:-?}" >&2; exit 1
    fi
    echo "$name: qp check ok, $now mutants killed (report: $out/CHECK.md)"
  fi
  repo="$work/$pname-proof"
  qp "qp assemble $pname $repo >/dev/null"
  cp -r "$exp/proof/." "$repo/"
  qp "cd $repo && git add -A src && git commit -qm 'LeanOS proof of $name' && qp verify --brief ." |
    tee "$work/verify-$name.out"
  # Keep qp verify's full report, which lives in the temporary workspace.
  report="$(sed -n 's/^The full report: //p' "$work/verify-$name.out" | tail -1)"
  out="$root/build/quickproof/$name"
  mkdir -p "$out"
  if [[ -n "$report" && -f "$report" ]]; then
    cp "$report" "$out/VERIFY.md"
    echo "$name: qp verify report: $out/VERIFY.md"
  fi
done
