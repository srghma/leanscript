### `SnapshotsPBOPure/`

| File | Recursive functions |
|---|---|
| [`CaptureDerefRegression01.lean`](SnapshotsPBOPure/CaptureDerefRegression01.lean) | 🟦 S `testEven` / `testOdd` (mutual, pattern on `n+1`) |
| [`CaseJacobs.lean`](SnapshotsPBOPure/CaseJacobs.lean) | 🟦 S `renderExpr` (pattern on `Expr` subtrees) |
| [`CaseLeafTco.lean`](SnapshotsPBOPure/CaseLeafTco.lean) | 🟦 S `test1Fuel` (pattern on `n+1`) |
| [`Fusion02.lean`](SnapshotsPBOPure/Fusion02.lean) | 🟥 W `toArrayLoop`, 🟥 W `filterMapStep` (`termination_by u.measure s`) |
| [`RecursionSchemes01.lean`](SnapshotsPBOPure/RecursionSchemes01.lean) | 🟦 S `cata` / `cataMap` (mutual, pattern on `FixExpr` / `ExprF FixExpr`) |
| [`Tco01.lean`](SnapshotsPBOPure/Tco01.lean) | 🟦 S `test` (pattern on `n+1`) |
| [`Tco03.lean`](SnapshotsPBOPure/Tco03.lean) | 🟥 W `go`, 🟥 W `k` (`termination_by n` / `termination_by m`, subtracts 1 without pattern match) |
| [`Tco04.lean`](SnapshotsPBOPure/Tco04.lean) | 🟥 W `test1` / `test2` (mutual, `termination_by n.toNat` / `m.toNat` on `Int`) |
| [`Tco05.lean`](SnapshotsPBOPure/Tco05.lean) | 🟥 W `go` (inner `let rec`, `i+1` bounded by `arr.size`, Lean infers well-founded) |
| [`Tco06.lean`](SnapshotsPBOPure/Tco06.lean) | 🟦 S `f` / `g` (mutual, pattern on `fuel+1`) |
| [`VanLaarhovenTraversals01.lean`](SnapshotsPBOPure/VanLaarhovenTraversals01.lean) | 🟦 S `traverseFun1` (pattern on `Fun`), 🟦 S `Fun.size` (pattern on `Fun`), 🟥 W `rewriteBottomUpM` (`termination_by t.size`) |

---

### `SnapshotsMy/`

| File | Recursive functions |
|---|---|
| [`AssignSteps.lean`](SnapshotsMy/AssignSteps.lean) | 🟦 S `test1`, `test2`, `test3`, `test4` (pattern on `fuel+1`) |
| [`GcdEntry.lean`](SnapshotsMy/GcdEntry.lean) | 🟥 W `Nat.gcd` (well-founded on remainder; ordinary function, ignoring `@[extern "lean_nat_gcd"]`) |
| [`HashContainers.lean`](SnapshotsMy/HashContainers.lean) | *(none)* |
| [`LoopEntry.lean`](SnapshotsMy/LoopEntry.lean) | 🟦 S `countUp`, 🟦 S `countdown` (pattern on `n+1`) |
| [`MutualSlots.lean`](SnapshotsMy/MutualSlots.lean) | 🟦 S `walkStr` / `walkNat` (mutual, pattern on `n+1`) |
| [`MutualTail.lean`](SnapshotsMy/MutualTail.lean) | 🟦 S `test1` / `test2` (mutual, pattern on `n+1`); 🟦 S `test3` / `test4` / `test5` (mutual, pattern on `n+1`) |
| [`ScalarRepl.lean`](SnapshotsMy/ScalarRepl.lean) | 🟦 S `clampSum` (pattern on `n+1`) |
| [`StringWalk.lean`](SnapshotsMy/StringWalk.lean) | 🟥 W `go` in `test1`, 🟥 W `go` in `test2` (`termination_by s.utf8ByteSize - p.byteIdx`); 🟥 W `go` in `test4` (inferred, `i+1` bounded by `s.length`) |
| [`TcoAck.lean`](SnapshotsMy/TcoAck.lean) | 🟥 W `ack` (`termination_by m n => (m, n)`); 🟦 S `ackInner` (pattern on `n+1`); 🟦 S `ack2` (pattern on `m+1`) |
| [`TcoBoom.lean`](SnapshotsMy/TcoBoom.lean) | 🟥 W `boom` (`termination_by n`, contradiction in `decreasing_by`) |
| [`TcoDiagonal.lean`](SnapshotsMy/TcoDiagonal.lean) | 🟥 W `diagonal`, 🟥 W `diagonal_tr` (`termination_by (m + n, m)`) |
| [`TcoHyper.lean`](SnapshotsMy/TcoHyper.lean) | 🟥 W `hyper` (`termination_by n _ b => (n, b)`); 🟦 S `hyperLoop` (pattern on `b+1`); 🟦 S `hyperTCO`, 🟦 S `hyperWhile` (pattern on `n+1`) |
| [`TcoMc91.lean`](SnapshotsMy/TcoMc91.lean) | 🟥 W `mc91Loop` (`termination_by c n => 2 * (111 - n) + 21 * c`); 🟦 S `iter` (pattern on `c+1`) |
