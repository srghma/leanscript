# Outputs of the earlier backend

These `FILE.js` files, with their `FILE.test.js` and `FILE.expected.js` companions, were
produced by an earlier Lean→JavaScript backend.  They were moved here, unchanged, when
`leanscript` started writing its own `FILE.js` (and `FILE-Term-unoptimized.txt`,
`FILE-Term-optimized.txt`, `FILE-MoreJsTy.txt`, `FILE.check.mjs`) next to each
`Tests/SnapshotsPBOPure/FILE.lean` that has at least one public, structurally total function.
The legacy files of the snapshots without such a function were left where they were.
The tests of the current output are the generated `FILE.check.mjs` modules
(`scripts/leanscript-snapshots.sh`).
