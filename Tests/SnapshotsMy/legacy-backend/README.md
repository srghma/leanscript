# Outputs of the earlier backend

These `.js` / `.test.js` files (and `Html-test-Program.txt`) were produced by an earlier
Lean→JavaScript backend (they import a `../runtime/` prelude that is no longer in the
project).  They were kept here, unchanged, when `leanscript` started writing its own
`FILE.js` next to each `Tests/SnapshotsMy/FILE.lean`.  The tests of the current output are
the generated `FILE.check.mjs` modules (`scripts/leanscript-snapshots.sh`).
