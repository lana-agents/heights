#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

config="${COMPARATOR_CONFIG_SOURCE:-Comparator/config.json}"
challenge="${COMPARATOR_CHALLENGE_SOURCE:-Comparator/Challenge.lean}"
solution="${COMPARATOR_SOLUTION_SOURCE:-Comparator/Solution.lean}"

python3 - "$config" "$challenge" "$solution" <<'PY'
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

config_path, challenge_path, solution_path = map(Path, sys.argv[1:])
for path in (config_path, challenge_path, solution_path):
    if not path.is_file():
        raise SystemExit(f"audit_comparator: missing input: {path}")

try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, json.JSONDecodeError) as error:
    raise SystemExit(f"audit_comparator: invalid config: {error}") from error

required = {
    "challenge_module",
    "solution_module",
    "theorem_names",
    "definition_names",
    "permitted_axioms",
}
if set(config) != required:
    missing = sorted(required - set(config))
    extra = sorted(set(config) - required)
    raise SystemExit(
        f"audit_comparator: config keys differ; missing={missing}, extra={extra}"
    )

identifier = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
def checked_names(key: str) -> list[str]:
    names = config[key]
    if not isinstance(names, list) or any(not isinstance(name, str) for name in names):
        raise SystemExit(f"audit_comparator: {key} must be an array of strings")
    if len(names) != len(set(names)):
        raise SystemExit(f"audit_comparator: {key} contains duplicates")
    invalid = [name for name in names if not identifier.fullmatch(name)]
    if invalid:
        raise SystemExit(f"audit_comparator: invalid Lean identifiers in {key}: {invalid}")
    return names

theorems = checked_names("theorem_names")
definitions = checked_names("definition_names")
if set(theorems) & set(definitions):
    raise SystemExit("audit_comparator: theorem and definition target names overlap")

for key in ("challenge_module", "solution_module"):
    if not isinstance(config[key], str) or not config[key]:
        raise SystemExit(f"audit_comparator: {key} must be a nonempty string")
axioms = config["permitted_axioms"]
if not isinstance(axioms, list) or any(not isinstance(name, str) for name in axioms):
    raise SystemExit("audit_comparator: permitted_axioms must be an array of strings")
if len(axioms) != len(set(axioms)):
    raise SystemExit("audit_comparator: permitted_axioms contains duplicates")

def declarations(path: Path, kind: str) -> list[str]:
    text = path.read_text(encoding="utf-8")
    if kind == "theorem":
        pattern = r"(?m)^theorem\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    else:
        pattern = r"(?m)^(?:noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    return re.findall(pattern, text)

challenge_theorems = declarations(challenge_path, "theorem")
solution_theorems = declarations(solution_path, "theorem")
challenge_definitions = declarations(challenge_path, "definition")
solution_definitions = declarations(solution_path, "definition")

missing_challenge = [name for name in theorems if name not in challenge_theorems]
if missing_challenge:
    raise SystemExit(
        f"audit_comparator: configured theorem(s) missing from challenge: {missing_challenge}"
    )
if solution_theorems != theorems:
    raise SystemExit(
        "audit_comparator: solution theorem declarations differ from config: "
        f"solution={solution_theorems}, config={theorems}"
    )
missing_challenge_defs = [name for name in definitions if name not in challenge_definitions]
missing_solution_defs = [name for name in definitions if name not in solution_definitions]
if missing_challenge_defs or missing_solution_defs:
    raise SystemExit(
        "audit_comparator: configured definition(s) missing: "
        f"challenge={missing_challenge_defs}, solution={missing_solution_defs}"
    )

print(
    "audit_comparator: config agrees with challenge and solution "
    f"({len(theorems)} theorem target(s), {len(definitions)} definition target(s))"
)
PY
