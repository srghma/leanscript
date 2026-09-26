#!/usr/bin/env python3
"""Stand-alone benchmark behind `proposals/ExternCatalogueSpeed.md`.

Writes three Lean files (no imports) into the directory given (default `/tmp/bench`):

* `big.lean`   -- one inductive with 460 two-argument constructors and an `eval` that is one
                  460-way `match` (the shape of `LeanInitPureExtern` / `Extern.eval`);
* `small.lean` -- the same with 8 constructors (the cost of the loop itself);
* `two.lean`   -- the 460 entries split into 20 inductives of 23, plus a 20-way wrapper
                  (the proposed two-level catalogue).

Each file ends with a kernel-only check (`decide +kernel`) that calls `eval` 3000 times.
Run with `lean <file>`; the profiler prints the kernel time of that check as the last
`type checking took ...` line.
"""
import os, sys

N_CALLS = 3000

def flat(n, name):
    s = "set_option profiler true\nset_option profiler.threshold 50\n"
    s += f"inductive {name} : Type where\n" + "".join(f"  | c{i} : Nat → Nat → {name}\n" for i in range(n))
    s += f"def {name}.eval : {name} → Nat\n" + "".join(f"  | .c{i} a b => a + b + {i}\n" for i in range(n))
    s += f"""
def loop : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc => loop k ({name}.eval (.c3 acc 1) % 1000)
set_option maxHeartbeats 0
theorem check : loop {N_CALLS} 0 = loop {N_CALLS} 0 + 0 := by decide +kernel
"""
    return s

def two(groups, per):
    s = "set_option profiler true\nset_option profiler.threshold 50\n"
    for g in range(groups):
        s += f"inductive G{g} : Type where\n" + "".join(f"  | c{i} : Nat → Nat → G{g}\n" for i in range(per))
        s += f"def G{g}.eval : G{g} → Nat\n" + "".join(f"  | .c{i} a b => a + b + {i}\n" for i in range(per))
    s += "inductive H : Type where\n" + "".join(f"  | g{g} : G{g} → H\n" for g in range(groups))
    s += "def H.eval : H → Nat\n" + "".join(f"  | .g{g} e => e.eval\n" for g in range(groups))
    s += f"""
def loop : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc => loop k (H.eval (.g0 (.c3 acc 1)) % 1000)
set_option maxHeartbeats 0
theorem check : loop {N_CALLS} 0 = loop {N_CALLS} 0 + 0 := by decide +kernel
"""
    return s

out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/bench"
os.makedirs(out, exist_ok=True)
open(os.path.join(out, "big.lean"), "w").write(flat(460, "E"))
open(os.path.join(out, "small.lean"), "w").write(flat(8, "F"))
open(os.path.join(out, "two.lean"), "w").write(two(20, 23))
print(f"wrote big.lean, small.lean, two.lean to {out}")
