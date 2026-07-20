#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

./scripts/audit_blueprint_links.sh

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/heights-blueprint-link-tests.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
fixture="$tmp_dir/Blueprint.lean"
cp Blueprint/HeightsBlueprint/Blueprint.lean "$fixture"

python3 - "$fixture" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
existing = 'lean := "Heights.normalizedLogHeight"'
missing = 'lean := "Heights.deliberatelyMissingBlueprintLinkFixture"'
if text.count(existing) != 1:
    raise SystemExit("test_audit_blueprint_links: fixture anchor is not unique")
path.write_text(text.replace(existing, missing), encoding="utf-8")
PY

if BLUEPRINT_LINK_SOURCE="$fixture" ./scripts/audit_blueprint_links.sh \
    >"$tmp_dir/missing.out" 2>&1; then
  echo "test_audit_blueprint_links: expected rejection for missing declaration" >&2
  exit 1
fi
if ! grep -q 'Unknown identifier.*Heights.deliberatelyMissingBlueprintLinkFixture' \
    "$tmp_dir/missing.out"; then
  echo "test_audit_blueprint_links: missing-declaration fixture failed for the wrong reason" >&2
  cat "$tmp_dir/missing.out" >&2
  exit 1
fi

echo "test_audit_blueprint_links: rejected a nonexistent linked declaration"
