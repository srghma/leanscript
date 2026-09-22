#!/usr/bin/env python3
"""Refresh the `#guard_msgs` expectations of the snapshot reports.

Each file of `SnapshotsMy/` and `SnapshotsPBOPure/` ends with one or both of

    /--
    info: …
    -/
    #guard_msgs in
    #leanjs_generate_term_and_ctx_for_all

    /--
    info: …
    -/
    #guard_msgs in
    #leanjs_compile_term_for_all

the first being a report on every public function of the file (see
`LeanScript.Term.Elab`) and the second the list of the ones that were compiled into a
`LeanScript.Expr.Term` (see `LeanScript.Term.Compile`).  This script strips the
expectations, rebuilds the two libraries to capture what the commands actually print,
and writes them back — so a change to either report is a reviewable diff rather than a
build failure.

Everything here works line by line and keeps track of how deep in a block comment it
is, because these files also hold *commented-out* copies of the same commands, which
must be left alone.

Run it from the root of the project:  python3 scripts/regen_snapshot_reports.py
"""
import glob, re, subprocess, sys, collections

FILES = sorted(glob.glob('SnapshotsMy/*.lean') + glob.glob('SnapshotsPBOPure/*.lean'))
CMDS = ['#leanjs_generate_term_and_ctx_for_all', '#leanjs_compile_term_for_all']


def command_lines(lines):
    """The indices of the lines that are one of the commands, outside a block comment."""
    spots, depth = [], 0
    for i, line in enumerate(lines):
        if line.strip() in CMDS and depth == 0:
            spots.append(i)
        depth += line.count('/-') - line.count('-/')
    return spots


def strip(path: str) -> bool:
    """Remove the `#guard_msgs` expectation in front of each live command."""
    lines = open(path).read().split('\n')
    if not command_lines(lines):
        return False
    for i in reversed(command_lines(lines)):
        # `/--` … `-/` `#guard_msgs in` <command>
        if i < 1 or lines[i - 1].strip() != '#guard_msgs in':
            continue
        j = i - 2
        if j < 0 or lines[j].strip() != '-/':
            continue
        start = j
        while start >= 0 and lines[start].strip() != '/--':
            start -= 1
        if start < 0:
            continue
        del lines[start:i]
    open(path, 'w').write('\n'.join(lines))
    return True


def main() -> int:
    targets = [f for f in FILES if strip(f)]
    r = subprocess.run(['lake', 'build', 'SnapshotsMy', 'SnapshotsPBOPure'],
                       capture_output=True, text=True)
    out = (r.stdout + r.stderr).split('\n')
    # (file, line) -> the messages the command on that line printed
    msgs: "collections.OrderedDict[tuple, list]" = collections.OrderedDict()
    cur = None
    for l in out:
        m = re.match(r'^info: (Snapshots\w+/\w+\.lean):(\d+):\d+: (.*)$', l)
        if m:
            cur = (m.group(1), int(m.group(2)))
            msgs.setdefault(cur, []).append([m.group(3)])
        elif cur and l.startswith('  ') and msgs[cur]:
            msgs[cur][-1].append(l)
        elif l[:1] in ('i', 'w', 'e', 'ℹ', '✔', '⚠', '✖'):
            cur = None
    for f in targets:
        lines = open(f).read().split('\n')
        # rewrite from the bottom, so that the line numbers above stay valid
        for i in reversed(command_lines(lines)):
            ms = msgs.get((f, i + 1))
            if not ms:
                print('no report for', f, 'at line', i + 1)
                continue
            body = '\n---\n'.join('info: ' + '\n'.join(m) for m in ms)
            lines[i:i] = ['/--', body, '-/', '#guard_msgs in']
        open(f, 'w').write('\n'.join(lines))
        print(f, 'updated')
    return 0


if __name__ == '__main__':
    sys.exit(main())
