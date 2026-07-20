#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
export LAKE_JOBS="${LAKE_JOBS:-6}"
lake build HeightsBlueprint
lake env lean --run HeightsBlueprintMain.lean --output _out/site
test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
