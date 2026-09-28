#!/usr/bin/env bash
# Run `leanscript --functions-only --check` on every `Tests/SnapshotsMy/*.lean` and
# `Tests/SnapshotsPBOPure/*.lean` that has at least one public total function (non-recursive
# or structurally recursive), writing next to each such file
#   FILE-Term-unoptimized.txt, FILE-Term-optimized.txt,
#   FILE-JsTerm-pbo.txt, FILE-JsTerm-faithful.txt, FILE-pbo.js, FILE-faithful.js,
#   FILE-pbo.check.mjs, FILE-faithful.check.mjs
# (a file without one gets no outputs), then run every check module with node.  Extra
# arguments are passed to leanscript.  Exits non-zero if a check fails.
set -uo pipefail
cd "$(dirname "$0")/.."
lake build leanscript > /dev/null
status=0
for f in Tests/SnapshotsMy/*.lean Tests/SnapshotsPBOPure/*.lean; do
  timeout 600 .lake/build/bin/leanscript --quiet --functions-only --check "$@" "$f" || status=1
  base="${f%.lean}"
  for preset in pbo faithful; do
    if [ -f "$base-$preset.check.mjs" ] && command -v node > /dev/null; then
      (cd "$(dirname "$f")" && node "$(basename "$base")-$preset.check.mjs") || status=1
    fi
  done
done
exit $status
