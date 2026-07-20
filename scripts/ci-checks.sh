#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"
export LAKE_JOBS=6

run_stage() {
  local name="$1"
  shift
  echo "ci-checks: START $name"
  if "$@"; then
    echo "ci-checks: PASS  $name"
  else
    local status=$?
    echo "ci-checks: FAIL  $name (exit $status)" >&2
    exit "$status"
  fi
}

build_root() {
  lake build
}

build_blueprint() {
  cd "$repo_root/Blueprint"
  lake build
}

check_comparator() {
  cd "$repo_root"
  lake env lean Comparator/Challenge.lean
  lake env lean Comparator/Solution.lean
}

check_trust() {
  cd "$repo_root"
  ./scripts/test_audit_trust.sh
}

check_axioms() {
  cd "$repo_root"
  ./scripts/test_audit_axioms.sh
  ./scripts/audit_axioms.sh
}

run_stage "root bounded build" build_root
run_stage "blueprint bounded build" build_blueprint
run_stage "comparator elaboration" check_comparator
run_stage "trust audit and negative fixtures" check_trust
run_stage "axiom audit and orphan fixture" check_axioms

echo "ci-checks: all stages passed with LAKE_JOBS=$LAKE_JOBS"
