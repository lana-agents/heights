#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if git ls-files --error-unmatch .pi/orchestration/taxis.env >/dev/null 2>&1; then
  echo "audit_trust: .pi/orchestration/taxis.env must never be tracked" >&2
  exit 1
fi

candidate_list="$(mktemp "${TMPDIR:-/tmp}/heights-trust-candidates.XXXXXX")"
trap 'rm -f "$candidate_list"' EXIT

# During an implementation round, include non-ignored untracked candidates as
# well as tracked files. After commit this is exactly the tracked project set.
git ls-files -co --exclude-standard -z > "$candidate_list"

python3 - "$repo_root" "$candidate_list" <<'PY'
from __future__ import annotations

import csv
import re
import sys
from collections import Counter
from pathlib import Path

root = Path(sys.argv[1])
candidate_file = Path(sys.argv[2])
exception_path = Path("scripts/trust-exceptions.tsv")

source_suffixes = {".lean", ".sh", ".toml", ".json", ".md", ".tsv", ".txt", ".yml", ".yaml"}
source_names = {"lean-toolchain", ".gitignore"}
registry = exception_path.as_posix()

raw_paths = candidate_file.read_bytes().split(b"\0")
paths: list[str] = []
for raw in raw_paths:
    if not raw:
        continue
    path = raw.decode("utf-8", errors="strict")
    p = Path(path)
    if path.startswith("references/"):
        continue
    if p.suffix in source_suffixes or p.name in source_names:
        paths.append(path)
paths = sorted(set(paths))

if registry not in paths:
    raise SystemExit("audit_trust: exception registry is missing from candidate files")

machine_home = "/" + "home" + "/"
machine_users = "/" + "Users" + "/"
allowed_tokens = {
    "axiom", "sorry", "admit", "native_decide", "implemented_by", "unsafe",
    machine_home, machine_users,
}
records: list[tuple[str, int, str, str]] = []
with (root / exception_path).open(encoding="utf-8", newline="") as stream:
    for row_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
        if not row or row[0].startswith("#"):
            continue
        if len(row) != 4:
            raise SystemExit(f"audit_trust: invalid exception record at {registry}:{row_number}")
        path, line_text, token, reason = row
        if not path or Path(path).is_absolute() or any(c in path for c in "*?[]{}"):
            raise SystemExit(f"audit_trust: exception path is not an exact relative file: {path!r}")
        if path.endswith("/") or "/../" in f"/{path}/" or "/./" in f"/{path}/":
            raise SystemExit(f"audit_trust: exception path is not normalized: {path!r}")
        try:
            line = int(line_text)
        except ValueError:
            raise SystemExit(f"audit_trust: exception line is not an integer: {line_text!r}")
        if line < 1 or token not in allowed_tokens or not reason.strip():
            raise SystemExit(f"audit_trust: incomplete exception at {registry}:{row_number}")
        if not (root / path).is_file():
            raise SystemExit(f"audit_trust: exception path is not a current file: {path}")
        records.append((path, line, token, reason))

record_keys = [(path, line, token) for path, line, token, _ in records]
if len(record_keys) != len(set(record_keys)):
    raise SystemExit("audit_trust: duplicate exact exception record")
record_reasons = {(path, line, token): reason for path, line, token, reason in records}
seen: Counter[tuple[str, int, str]] = Counter()
failures: list[str] = []

trust_re = re.compile(r"(?<![A-Za-z0-9_])(axiom|sorry|admit|native_decide|implemented_by|unsafe)(?![A-Za-z0-9_])")
machine_re = re.compile(r"/(home|Users)/")
private_key_re = re.compile("-----BEGIN " + r"(?:RSA |EC |OPENSSH |DSA )?PRIVATE KEY-----")
taxis_re = re.compile(r"issues_pat_[A-Za-z0-9]{20,}")
github_re = re.compile(r"(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,})")
assignment_re = re.compile(
    r"(?i)(?:api[_-]?key|access[_-]?token|auth(?:orization)?|password|passwd|secret|token)"
    r"\s*[:=]\s*(?:\"(?!\$)[^\"]+\"|'(?!\$)[^']+'|"
    r"[A-Za-z0-9][A-Za-z0-9_./+\-=]{7,})"
)
credential_url_re = re.compile(r"https?://[^\s/:@]+:[^\s/@]+@[^\s]+")

def accept_or_reject(path: str, line: int, token: str, description: str) -> None:
    key = (path, line, token)
    if key in record_reasons:
        seen[key] += 1
    else:
        failures.append(f"{description}: {path}:{line}: {token}")

for path in paths:
    data = (root / path).read_bytes()
    if b"\0" in data:
        continue
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        continue
    lines = text.splitlines()

    if path.endswith(".lean"):
        for line_number, line in enumerate(lines, 1):
            for match in trust_re.finditer(line):
                accept_or_reject(path, line_number, match.group(1), "rejected Lean trust token")

    # The registry legitimately names the machine-path literals in its token
    # column, so exempt only that one scan. Credential checks below still apply
    # to every registry line exactly as they do to every other candidate file.
    for line_number, line in enumerate(lines, 1):
        if path != registry:
            for match in machine_re.finditer(line):
                accept_or_reject(path, line_number, f"/{match.group(1)}/", "rejected machine-local path")
        if private_key_re.search(line):
            failures.append(f"rejected private-key marker: {path}:{line_number}")
        if taxis_re.search(line):
            failures.append(f"rejected taxis-token-shaped string: {path}:{line_number}")
        if github_re.search(line):
            failures.append(f"rejected provider-token-shaped string: {path}:{line_number}")
        if assignment_re.search(line):
            failures.append(f"rejected credential assignment: {path}:{line_number}")
        if credential_url_re.search(line):
            failures.append(f"rejected credential-bearing URL: {path}:{line_number}")

for path, line, token, _reason in records:
    count = seen[(path, line, token)]
    if count != 1:
        failures.append(
            f"exception must match exactly one current occurrence (matched {count}): "
            f"{path}:{line}: {token}"
        )

challenge = root / "Comparator/Challenge.lean"
if not challenge.is_file():
    failures.append("Comparator/Challenge.lean is missing")
else:
    challenge_text = challenge.read_text(encoding="utf-8")
    targets = [
        "rat_height_scaled_denominator",
        "weighted_log_one_add_average",
        "modular_delta_j_fd_comparison",
        "modular_j_surjective",
        "modular_height_metric_eq_of_same_j",
        "silverman_proposition_2_1_certified",
    ]
    declarations = re.findall(r"(?m)^theorem\s+([A-Za-z0-9_']+)", challenge_text)
    if declarations != targets:
        failures.append(f"challenge theorem list differs from reviewed target list: {declarations!r}")
    for index, target in enumerate(targets):
        start = re.search(rf"(?m)^theorem\s+{re.escape(target)}\b", challenge_text)
        if start is None:
            continue
        next_starts = [
            match.start() for match in re.finditer(r"(?m)^theorem\s+", challenge_text)
            if match.start() > start.start()
        ]
        end = min(next_starts) if next_starts else len(challenge_text)
        count = len(re.findall(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", challenge_text[start.start():end]))
        if count != 1:
            failures.append(f"challenge target {target} has {count} proof placeholders, expected one")

if failures:
    for failure in failures:
        print(f"audit_trust: {failure}", file=sys.stderr)
    print("audit_trust: trust audit failed", file=sys.stderr)
    raise SystemExit(1)

print(
    f"audit_trust: passed ({len(paths)} source/control files; "
    f"{len(records)} exact reviewed exceptions, each used once)"
)
PY
