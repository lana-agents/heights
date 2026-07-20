#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

./scripts/audit_trust.sh

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/heights-trust-tests.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
copy="$tmp_dir/repo"
mkdir -p "$copy"

# Copy precisely tracked and non-ignored candidate files, never ignored secrets
# or build products. The temporary repository makes each negative fixture a
# genuinely tracked file without contaminating the real index or worktree.
git ls-files -co --exclude-standard -z | tar --null -T - -cf - | tar -C "$copy" -xf -
(
  cd "$copy"
  git init -q
  git add .
  ./scripts/audit_trust.sh >/dev/null
)

expect_rejection() {
  local label="$1" path="$2"
  shift 2
  (
    cd "$copy"
    rm -f AuditFixture.lean AuditFixture.toml AuditFixture.md
    "$@" > "$path"
    git add "$path"
    if ./scripts/audit_trust.sh >"$tmp_dir/$label.out" 2>&1; then
      echo "test_audit_trust: expected rejection for $label" >&2
      exit 1
    fi
    git reset -q HEAD -- "$path"
    rm -f "$path"
  )
  echo "test_audit_trust: rejected $label fixture"
}

expect_rejection axiom AuditFixture.lean printf '%s\n' 'axiom strayAxiom : True'
expect_rejection proof-hole AuditFixture.lean printf '%s\n' 'theorem strayHole : True := by sorry'

fake_prefix='FAKE_CREDENTIAL_'
expect_rejection credential AuditFixture.toml printf '%s\n' \
  "api_token = \"${fake_prefix}NOT_REAL_0123456789\""

home_component='home'
expect_rejection machine-path AuditFixture.md printf '%s\n' \
  "synthetic path: /${home_component}/not-a-real-user/project"

# Keep the registry structurally valid while planting a synthetic credential in
# one reason field.  Its key is split in this tracked harness so the harness is
# not itself a credential-shaped fixture.
(
  cd "$copy"
  registry='scripts/trust-exceptions.tsv'
  cp "$registry" "$tmp_dir/trust-exceptions.backup"
  fake_key='api_''token'
  fake_value='FAKE_REGISTRY_NOT_REAL_0123456789'
  python3 - "$registry" "$fake_key" "$fake_value" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
key, value = sys.argv[2:]
lines = path.read_text(encoding="utf-8").splitlines()
for index, line in enumerate(lines):
    if line and not line.startswith("#"):
        lines[index] = line + f' ({key} = "{value}")'
        break
path.write_text("\n".join(lines) + "\n", encoding="utf-8")
PY
  git add "$registry"
  if ./scripts/audit_trust.sh >"$tmp_dir/registry-credential.out" 2>&1; then
    echo "test_audit_trust: expected rejection for registry credential" >&2
    exit 1
  fi
  if ! grep -q 'rejected credential assignment: scripts/trust-exceptions.tsv:' \
      "$tmp_dir/registry-credential.out"; then
    echo "test_audit_trust: registry fixture failed for the wrong reason" >&2
    cat "$tmp_dir/registry-credential.out" >&2
    exit 1
  fi
  cp "$tmp_dir/trust-exceptions.backup" "$registry"
  git add "$registry"
)
echo "test_audit_trust: rejected credential fixture inside exceptions registry"

echo "test_audit_trust: positive path and all five negative cases passed"
