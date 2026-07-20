#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

AUDIT_AXIOMS_COVERAGE_ONLY=1 ./scripts/audit_axioms.sh

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/heights-axiom-tests.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
copy="$tmp_dir/repo"
mkdir -p "$copy"

# Recreate the candidate project in a temporary repository so the orphan is
# genuinely tracked while the real index and worktree remain untouched.
git ls-files -co --exclude-standard -z | tar --null -T - -cf - | tar -C "$copy" -xf -
(
  cd "$copy"
  git init -q
  git add .
  mkdir -p Heights
  printf '%s\n' 'def orphanImportCoverageFixture : Nat := 0' > Heights/Orphan.lean
  git add Heights/Orphan.lean
  if AUDIT_AXIOMS_COVERAGE_ONLY=1 ./scripts/audit_axioms.sh \
      >"$tmp_dir/orphan.out" 2>&1; then
    echo "test_audit_axioms: expected rejection for tracked orphan source" >&2
    exit 1
  fi
  if ! grep -q \
      'unimported project Lean source: Heights/Orphan.lean (not reachable from Heights.lean)' \
      "$tmp_dir/orphan.out"; then
    echo "test_audit_axioms: orphan fixture failed for the wrong reason" >&2
    cat "$tmp_dir/orphan.out" >&2
    exit 1
  fi
)

echo "test_audit_axioms: rejected tracked, unimported Heights/Orphan.lean fixture"
