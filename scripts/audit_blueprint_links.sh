#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

blueprint="${BLUEPRINT_LINK_SOURCE:-Blueprint/HeightsBlueprint/Blueprint.lean}"
if [[ ! -f "$blueprint" ]]; then
  echo "audit_blueprint_links: missing blueprint source: $blueprint" >&2
  exit 1
fi

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/heights-blueprint-links.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
checks="$tmp_dir/BlueprintLinkChecks.lean"
manifest="$tmp_dir/declarations.txt"

python3 - "$blueprint" "$checks" "$manifest" <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

source = Path(sys.argv[1])
checks = Path(sys.argv[2])
manifest = Path(sys.argv[3])
text = source.read_text(encoding="utf-8")

# Verso blueprint declaration links use a comma-separated string. Match across
# line breaks, but deliberately reject escapes: declaration names need none,
# and accepting them would make generation of the Lean check file ambiguous.
annotation = re.compile(r'\blean\s*:=\s*"([^"\\]*)"', re.DOTALL)
tokens = list(re.finditer(r'\blean\s*:=', text))
matches = list(annotation.finditer(text))
if len(matches) != len(tokens):
    raise SystemExit(
        "audit_blueprint_links: found a malformed or escaped lean := annotation "
        f"({len(tokens)} token(s), {len(matches)} parseable annotation(s))"
    )
if not matches:
    raise SystemExit("audit_blueprint_links: no lean := annotations found")

# Blueprint links are intentionally restricted to this project's public API.
# This also makes interpolating names into #check commands safe.
valid_name = re.compile(
    r"^Heights\.[A-Za-z_][A-Za-z0-9_']*"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
names: list[str] = []
for match in matches:
    fields = [field.strip() for field in match.group(1).split(",")]
    if not fields or any(not field for field in fields):
        raise SystemExit(
            "audit_blueprint_links: empty declaration in lean := annotation at "
            f"{source}:{text.count(chr(10), 0, match.start()) + 1}"
        )
    for name in fields:
        if not valid_name.fullmatch(name):
            raise SystemExit(
                "audit_blueprint_links: invalid project declaration name "
                f"{name!r} at {source}:"
                f"{text.count(chr(10), 0, match.start()) + 1}"
            )
        names.append(name)

manifest.write_text("\n".join(names) + "\n", encoding="utf-8")
checks.write_text(
    "import Heights\n\n" + "\n".join(f"#check {name}" for name in names) + "\n",
    encoding="utf-8",
)
print(
    f"audit_blueprint_links: extracted {len(names)} declaration link(s) "
    f"from {len(matches)} annotation(s)"
)
PY

export LAKE_JOBS="${LAKE_JOBS:-6}"
if ! lake env lean "$checks" >"$tmp_dir/lean.out" 2>&1; then
  echo "audit_blueprint_links: at least one linked Lean declaration does not resolve" >&2
  cat "$tmp_dir/lean.out" >&2
  exit 1
fi

echo "audit_blueprint_links: every linked declaration resolves in the Heights environment"
