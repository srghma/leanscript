#!/usr/bin/env bash
# Run `leanscript --check` on every `Tests/SnapshotsMy/*.lean` (writing FILE-Term-unoptimized.txt,
# FILE-Term-optimized.txt, FILE-MoreJsTy.txt, FILE.js and FILE.check.mjs next to each file),
# then run every check module with node.  Extra arguments are passed to leanscript
# (e.g. `--preset=pbo`).  Exits non-zero if a check fails.
set -uo pipefail
cd "$(dirname "$0")/.."
bash scripts/install-leanscript.sh > /dev/null
status=0
for f in Tests/SnapshotsMy/*.lean; do
  timeout 600 .lake/bin/leanscript --quiet --check "$@" "$f" || status=1
  base="${f%.lean}"
  if [ -f "$base.check.mjs" ] && command -v node > /dev/null; then
    (cd "$(dirname "$f")" && node "$(basename "$base").check.mjs") || status=1
  fi
done
exit $status
