#!/usr/bin/env bash
# Run `leanscript --functions-only --check` on every `Tests/SnapshotsMy/*.lean` and
# `Tests/SnapshotsPBOPure/*.lean` that has at least one public total function (structurally
# recursive or defined by well-founded recursion)
# (writing FILE-Term-unoptimized.txt, FILE-Term-optimized.txt, FILE-JsTerm.txt, FILE.js and
# FILE.check.mjs next to each such file; a file without one gets no outputs),
# then run every check module with node.  Extra arguments are passed to leanscript
# (e.g. `--preset=pbo`).  Exits non-zero if a check fails.
set -uo pipefail
cd "$(dirname "$0")/.."
bash scripts/install-leanscript.sh > /dev/null
status=0
for f in Tests/SnapshotsMy/*.lean Tests/SnapshotsPBOPure/*.lean; do
  timeout 600 .lake/bin/leanscript --quiet --functions-only --check "$@" "$f" || status=1
  base="${f%.lean}"
  if [ -f "$base.check.mjs" ] && command -v node > /dev/null; then
    (cd "$(dirname "$f")" && node "$(basename "$base").check.mjs") || status=1
  fi
done
exit $status
