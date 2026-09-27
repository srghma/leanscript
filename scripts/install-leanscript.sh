#!/usr/bin/env bash
# Build the `leanscript` executable and make it available as `./.lake/bin/leanscript`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build leanscript
mkdir -p .lake/bin
ln -sf ../build/bin/leanscript .lake/bin/leanscript
echo "installed .lake/bin/leanscript -> .lake/build/bin/leanscript"
