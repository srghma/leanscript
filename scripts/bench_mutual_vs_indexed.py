#!/usr/bin/env python3
"""Stand-alone benchmark behind section 3 of `proposals/BuildSpeedProposals.md`.

It compares two ways of declaring a family of mutually recursive types. The first is a
`mutual` block of N inductives, which is the shape of `LeanScript/Expr/Term.lean`: 28 types,
136 constructors. The second is one inductive indexed by a tag, so a single type stands for
the whole block.

Writes four Lean files (no imports) into the directory given (default `/tmp/bench`):

* `mutual.lean`   -- N mutual inductives with M+1 constructors each (declaration only);
* `indexed.lean`  -- the same constructors as one inductive `U : K → Type` (declaration only);
* `mutual2.lean`  -- as `mutual.lean`, plus a structurally recursive `sz` (N mutual
                     functions), a builder, and a `decide +kernel` evaluation check;
* `indexed2.lean` -- the same for the indexed encoding (one function `U.sz`).

Run each with `lean -Dprofiler=true <file>` and compare the `type checking` and
`elaboration` totals.

Usage: python3 scripts/bench_mutual_vs_indexed.py [dir] [N=28] [M=4] [depth=10]
"""
import os, sys

out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/bench"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 28
M = int(sys.argv[3]) if len(sys.argv) > 3 else 4
D = int(sys.argv[4]) if len(sys.argv) > 4 else 10
os.makedirs(out, exist_ok=True)


def edges(i, j):
    return (i + j) % N, (i + 2 * j + 1) % N


def write(name, lines):
    with open(os.path.join(out, name), "w") as f:
        f.write("\n".join(lines) + "\n")


# 1. declarations only, with a Nat index (like `Term`'s indices)
L = ["set_option autoImplicit false", "mutual"]
for i in range(N):
    L.append(f"inductive T{i} : Nat → Type")
    for j in range(M):
        a, b = edges(i, j)
        L.append(f"  | c{j} (n : Nat) : T{a} n → T{b} (n+1) → T{i} n")
    L.append(f"  | leaf (n : Nat) : T{i} n")
L.append("end")
write("mutual.lean", L)

L = ["set_option autoImplicit false", f"inductive K | mk (tag : Fin {N}) (n : Nat)", "inductive U : K → Type"]
for i in range(N):
    for j in range(M):
        a, b = edges(i, j)
        L.append(f"  | t{i}c{j} (n : Nat) : U ⟨{a}, n⟩ → U ⟨{b}, n+1⟩ → U ⟨{i}, n⟩")
    L.append(f"  | t{i}leaf (n : Nat) : U ⟨{i}, n⟩")
write("indexed.lean", L)

# 2. declarations + structural recursion + a kernel evaluation
L = ["set_option autoImplicit false", "mutual"]
for i in range(N):
    L.append(f"inductive T{i} : Type")
    for j in range(M):
        a, b = edges(i, j)
        L.append(f"  | c{j} : T{a} → T{b} → T{i}")
    L.append(f"  | leaf : T{i}")
L.append("end")
L.append("mutual")
for i in range(N):
    L.append(f"def T{i}.sz : T{i} → Nat")
    for j in range(M):
        L.append(f"  | .c{j} x y => x.sz + y.sz + 1")
    L.append("  | .leaf => 1")
L.append("end")
L.append("mutual")
for i in range(N):
    a, b = edges(i, 0)
    L.append(f"def T{i}.mk : Nat → T{i}\n  | 0 => .leaf\n  | n+1 => .c0 (T{a}.mk n) (T{b}.mk n)")
L.append("end")
L.append(f"set_option maxRecDepth 100000 in\nexample : (T0.mk {D}).sz = {2**(D+1)-1} := by decide +kernel")
write("mutual2.lean", L)

L = ["set_option autoImplicit false", f"inductive U : Fin {N} → Type"]
for i in range(N):
    for j in range(M):
        a, b = edges(i, j)
        L.append(f"  | t{i}c{j} : U {a} → U {b} → U {i}")
    L.append(f"  | t{i}leaf : U {i}")
L.append(f"def U.sz : {{k : Fin {N}}} → U k → Nat")
for i in range(N):
    for j in range(M):
        L.append(f"  | _, .t{i}c{j} x y => x.sz + y.sz + 1")
    L.append(f"  | _, .t{i}leaf => 1")
L.append(f"def U.mk : (k : Fin {N}) → Nat → U k")
for i in range(N):
    a, b = edges(i, 0)
    L.append(f"  | ⟨{i}, _⟩, 0 => .t{i}leaf")
    L.append(f"  | ⟨{i}, _⟩, n+1 => .t{i}c0 (U.mk {a} n) (U.mk {b} n)")
L.append(f"  | ⟨_+{N}, h⟩, _ => absurd h (by omega)")
L.append(f"set_option maxRecDepth 100000 in\nexample : (U.mk 0 {D}).sz = {2**(D+1)-1} := by decide +kernel")
write("indexed2.lean", L)

print(f"wrote mutual.lean, indexed.lean, mutual2.lean, indexed2.lean to {out} (N={N}, M={M}, depth={D})")
