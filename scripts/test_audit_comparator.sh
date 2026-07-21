#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

./scripts/audit_comparator.sh

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/heights-comparator-tests.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
fixture="$tmp_dir/config.json"
cp Comparator/config.json "$fixture"

python3 - "$fixture" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
config = json.loads(path.read_text(encoding="utf-8"))
config["theorem_names"].append("deliberately_missing_comparator_target")
path.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

if COMPARATOR_CONFIG_SOURCE="$fixture" ./scripts/audit_comparator.sh \
    >"$tmp_dir/missing.out" 2>&1; then
  echo "test_audit_comparator: expected rejection for a missing target" >&2
  exit 1
fi
if ! grep -q 'configured theorem(s) missing from challenge' "$tmp_dir/missing.out"; then
  echo "test_audit_comparator: missing-target fixture failed for the wrong reason" >&2
  cat "$tmp_dir/missing.out" >&2
  exit 1
fi

echo "test_audit_comparator: rejected a configured target absent from the challenge"
