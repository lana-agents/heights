#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

check_import_coverage() {
  local candidates
  candidates="$(mktemp "${TMPDIR:-/tmp}/heights-import-candidates.XXXXXX")"
  git ls-files -co --exclude-standard -z -- '*.lean' > "$candidates"
  python3 - "$repo_root" "$candidates" <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
candidate_file = Path(sys.argv[2])
paths = {
    raw.decode("utf-8")
    for raw in candidate_file.read_bytes().split(b"\0")
    if raw
}

# These are the two logical environments audited by AuditAxioms.lean.
# Comparator/Challenge.lean is intentionally a separate, sorried environment;
# Blueprint and scripts are tooling packages rather than project theorem roots.
heights_sources = {
    path for path in paths
    if path == "Heights.lean" or (path.startswith("Heights/") and path.endswith(".lean"))
}
solution_sources = {
    path for path in paths
    if path == "Comparator/Solution.lean" or (
        path.startswith("Comparator/") and path.endswith(".lean")
        and path != "Comparator/Challenge.lean"
    )
}

required_roots = {"Heights.lean", "Comparator/Solution.lean"}
missing_roots = sorted(required_roots - paths)
if missing_roots:
    raise SystemExit(
        "audit_axioms: missing audited import root(s): " + ", ".join(missing_roots)
    )

def module_name(path: str) -> str:
    relative = path[:-5]
    if path.startswith("Comparator/"):
        relative = relative[len("Comparator/"):]
    return relative.replace("/", ".")

module_paths = {module_name(path): path for path in paths if path.endswith(".lean")}
import_re = re.compile(r"^\s*import\s+(.+?)\s*$")

def uncommented_lines(text: str) -> list[str]:
    lines: list[str] = []
    depth = 0
    for line in text.splitlines():
        code: list[str] = []
        index = 0
        while index < len(line):
            if depth:
                if line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            elif line.startswith("--", index):
                break
            elif line.startswith("/-", index):
                depth = 1
                index += 2
            else:
                code.append(line[index])
                index += 1
        lines.append("".join(code))
    return lines

def direct_imports(path: str) -> list[str]:
    imports: list[str] = []
    text = (root / path).read_text(encoding="utf-8")
    for line in uncommented_lines(text):
        match = import_re.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports

def closure(start: str) -> set[str]:
    reached: set[str] = set()
    pending = [start]
    while pending:
        path = pending.pop()
        if path in reached:
            continue
        reached.add(path)
        for imported in direct_imports(path):
            imported_path = module_paths.get(imported)
            if imported_path is not None and imported_path not in reached:
                pending.append(imported_path)
    return reached

checks = [
    ("Heights.lean", heights_sources),
    ("Comparator/Solution.lean", solution_sources),
]
failures: list[str] = []
for import_root, expected in checks:
    for path in sorted(expected - closure(import_root)):
        failures.append(
            f"audit_axioms: unimported project Lean source: {path} "
            f"(not reachable from {import_root})"
        )
if failures:
    raise SystemExit("\n".join(failures))

print(
    "audit_axioms: import coverage includes "
    f"{len(heights_sources)} Heights source(s) and "
    f"{len(solution_sources)} Solution source(s)"
)
PY
  rm -f "$candidates"
}

check_import_coverage
if [[ "${AUDIT_AXIOMS_COVERAGE_ONLY:-0}" == 1 ]]; then
  exit 0
fi

export LAKE_JOBS="${LAKE_JOBS:-6}"
lake build Heights Solution

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/heights-axioms.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
manifest="$tmp_dir/compiled-manifest.txt"
visited="$tmp_dir/visited-manifest.txt"
output="$tmp_dir/audit-output.txt"

HEIGHTS_AUDIT_MODE=manifest HEIGHTS_AUDIT_OUTPUT="$manifest" \
  lake env lean scripts/AuditAxioms.lean
HEIGHTS_AUDIT_MODE=visited HEIGHTS_AUDIT_OUTPUT="$visited" \
  lake env lean scripts/AuditAxioms.lean

if ! diff -u "$manifest" "$visited"; then
  echo "audit_axioms: compiled-module and environment-walk manifests differ" >&2
  exit 1
fi

# The empty P1 manifest is deliberate and is still checked by the diff above.
# Named public project declarations begin to populate it in P2.
count="$(wc -l < "$manifest" | tr -d ' ')"
if [[ ! -s "$manifest" ]]; then
  count=0
fi
echo "audit_axioms: coverage manifests agree on $count declaration(s)"

lake env lean scripts/AuditAxioms.lean | tee "$output"
if ! grep -q "AXIOM_AUDIT|SUMMARY|$count" "$output"; then
  echo "audit_axioms: missing or inconsistent machine-stable summary marker" >&2
  exit 1
fi
if grep -q '^AXIOM_AUDIT|DECL|.*Challenge' "$output"; then
  echo "audit_axioms: challenge-hole dependency leaked through Solution" >&2
  exit 1
fi

echo "audit_axioms: every covered declaration uses only the permitted axiom subset"
