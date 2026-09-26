#!/usr/bin/env bash
# Profile every module of the project, one `lean -Dprofiler=true` run each, and print a
# table of wall time, import time, elaboration, kernel type checking and tactic time.
# Used for `proposals/BuildSpeedProposals.md`. Run `lake build` first, so every import
# has an .olean.
#
# Usage: scripts/profile_modules.sh [jobs=4] [outdir=/tmp/prof]
set -euo pipefail
JOBS=${1:-4}
OUT=${2:-/tmp/prof}
cd "$(dirname "$0")/.."
mkdir -p "$OUT"
# `lake env` costs several seconds per call, so read LEAN_PATH once.
export LEAN_PATH=$(lake env printenv LEAN_PATH)
export OUT
find LeanScript TyTests TermTests NonEmpty -name '*.lean' | xargs -P"$JOBS" -I{} bash -c '
  f={}; o="$OUT/$(echo "$f" | tr / _).out"
  s=$(date +%s%N); lean -Dprofiler=true "$f" > "$o" 2>&1 || true; e=$(date +%s%N)
  echo "wall $(( (e-s)/1000000 ))" >> "$o"'
python3 - "$OUT" <<'EOF'
import re, glob, sys, os
def sec(s):
    v = float(re.match(r'[0-9.]+', s).group()); return v/1000 if s.endswith('ms') else v
rows = []
for f in glob.glob(os.path.join(sys.argv[1], '*.out')):
    txt = open(f).read()
    cats = {c: sec(v) for c, v in re.findall(r'^\t([a-zA-Z ()\-]+?) ([0-9.]+m?s)$', txt, re.M)}
    wall = int(re.search(r'wall (\d+)', txt).group(1)) / 1000
    rows.append((wall, cats.get('import', 0), cats.get('elaboration', 0),
                 cats.get('type checking', 0), cats.get('tactic execution', 0),
                 os.path.basename(f)[:-4].replace('_', '/')))
rows.sort(reverse=True)
print(f"{'wall':>6} {'import':>6} {'elab':>6} {'kernel':>6} {'tactic':>6}  module")
for r in rows:
    print("%6.1f %6.1f %6.1f %6.1f %6.1f  %s" % r)
W = sum(r[0] for r in rows); I = sum(r[1] for r in rows)
print("total wall %.0f s, of which import %.0f s (%.0f%%), %d modules" % (W, I, 100*I/W, len(rows)))
EOF
