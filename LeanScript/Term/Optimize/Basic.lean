module

public import LeanScript.Term.Optimize.Cse
public import LeanScript.Term.Optimize.Hoist
public import LeanScript.Term.Optimize.FieldsWalk
public import LeanScript.Term.Optimize.KnownTest
public import LeanScript.Term.Optimize.KnownSize
public import LeanScript.Term.Optimize.Cond
public import LeanScript.Term.Optimize.ShareTest
public import LeanScript.Term.Optimize.MergeTest
public import LeanScript.Term.Optimize.ZipTest
public import LeanScript.Term.Optimize.Append
public import LeanScript.Term.Optimize.KnownLit
public import LeanScript.Term.Optimize.Arith
public import LeanScript.Term.Optimize.InlineEval
public import LeanScript.Term.Optimize.InlineRetEval
public import LeanScript.Term.Optimize.JoinCtorEval
public import LeanScript.Term.Optimize.LoopYieldEval
public import LeanScript.Term.Optimize.OpenCallEval
public import LeanScript.Term.Optimize.DelayEtaEval
public import LeanScript.Term.Optimize.SinkLet
public import LeanScript.Term.Optimize.CondJumpEval

@[expose] public section

set_option autoImplicit false

/-!
# An optimiser for normal-form terms

`Term.optimize t` rewrites a statement into one with the same value (`Term.optimize_eval`,
`Term.optimize_run`).  It walks the statement like `Term.eval` does (values, bodies,
computations, statements, branches), and then runs dead-code elimination (`Term.dce`), which
also recounts the usages.  The rewrites, all of which only ever *remove* work:

* **copy propagation**: `let x := share y; b`, where `y` is an unknown of the same level as
  `x`, becomes `b` with `x` renamed to `y` (`URen.subst`);
* **a shared answer is the answer**: `let x := share n; ret x` becomes `ret n`, and
  `let x := share n; jump j x` becomes `jump j n` (the neutral expression `n` is computed once
  either way, and nothing else reads `x`);
* **dead case analysis**: `record_casesOn us n b` where `b` reads none of the fields becomes
  `b` (the language is pure and total, so taking a record apart for nothing is dead code);

Then the known fields (`LeanScript.Term.Optimize.Fields`): every record case analysis binds all
its fields (`Term.widenFields`), and a case analysis of an unknown record whose fields are
already bound is dropped, its fields renamed to the ones already bound (`Term.reuseFields`:
`let ⟨a, b⟩ := x; …; let ⟨c, d⟩ := x; body` is `let ⟨a, b⟩ := x; …; body[c := a, d := b]`).

Then the tests whose answer is already known are dropped (`Term.knownTests`,
`LeanScript.Term.Optimize.KnownTest`): inside an arm of `if x` (`x` a boolean unknown, or its
negation) the value of `x` is known, so `if x then (if x then X else Y) else Z` is
`if x then X else Z`, and `ret (x ? a : b)` there is `ret a`.  A join point whose test jumps
to it with the same argument in both arms is its body (`Term.joinSame`).

Then a test that both arms of an `if` begin with, and that leads to the same answer (or jump)
in both, is made first (`Term.shareTestWalk`, `LeanScript.Term.Optimize.ShareTest`):
`if p then (if q then X else Y) else (if q then X else Z)` is
`if q then X else if p then Y else Z` (never more tests on any path, `X` written once).

Then, when both arms of an `if p` make the same tests (the same conditions and record case
analyses, in the same order) and differ only in their answers, `p` is pushed into the answers
(`Term.zipTestWalk`, `LeanScript.Term.Optimize.ZipTest`):
`if p then (if q then a else b) else (if q then c else d)` is
`if q then (p ? a : c) else (p ? b : d)` (never more tests on any path, the shared tests
written once).

Then the dead bindings are dropped (`Term.dce`), so that a computation the statement never uses
does not make the walks below share (and so compute on every path) a computation that is
otherwise made in one arm only.  Then another walk (`Term.cseWalk`) does the rewrites of `LeanScript.Term.Optimize.Cse`:

* **common subexpressions** (`Term.cseLetE`): a simple computation (`f a`, `t ()`, `force t`
  on atoms) repeated at the same depth in the scope of its first occurrence is computed once;
* **identical branches** (`Term.mkBranch`): `if c then ret a else ret a` is `ret a`, and
  `if c then ret a else ret b` is `ret (c ? a : b)` (the pure conditional `Neu.cond`);
* **trivial join points** (`Branch.mkJoin`): a join point whose body is `ret a` (an atom) or
  `ret x` (its parameter) is inlined into its jumps and dropped.

Then the hoisting walk (`Term.hoistWalk`, `LeanScript.Term.Optimize.Hoist`): a call of an extern
on atoms (`toString x`) that every path of a statement computes, and that occurs at least twice
in it, is computed once in front of it and named (`let y := toString x; if c then y ++ y else
f y`); no path computes more than before.

Then the boolean conditions (`Term.condWalk`, `LeanScript.Term.Optimize.Cond`):
`c ? true : false` is `c`, and a negated condition (`c ? false : true`) of a conditional or of
an `if` is read as `c` with the two branches swapped.

Then two tests that end in the same answer (or jump) are merged into one condition
(`Term.mergeTestWalk`, `LeanScript.Term.Optimize.MergeTest`):
`if p then (if q then X else E) else E` is `if (p && q) then X else E`, and
`if p then E else (if q then E else X)` is `if (p || q) then E else X` (with `!q` when `E` is
the other arm of the inner test; an inner test may be a conditional answer `ret (q ? a : b)`;
`p && q` is the pure conditional `p ? q : false`, `p || q` is `p ? true : q`).

Then the known constant literals (`Term.knownLits`, `LeanScript.Term.Optimize.KnownLit`): an
operand of an append that names a `val` of a constant array or list literal is the literal
itself (`val k := #["a"]; k ++ xs` is `#["a"] ++ xs`), so that the append chains can merge it.

Then the append chains (`Term.appendWalk`, `LeanScript.Term.Optimize.Append`): a chain of
`Array.append`s is regrouped to the left and one of `List.append`s to the right, its empty
literals are dropped and neighbouring literals are merged (`#[a] ++ (#[b] ++ x) ++ #[c]` is
`(#[a, b] ++ x) ++ #[c]`, `[a] ++ ([b] ++ x) ++ [c]` is `[a, b] ++ (x ++ [c])`); a chain of
`String.append`s (and of `String.push`es of a literal character) is regrouped to the left, its
empty literals dropped and neighbouring literals merged (`"a" ++ ("b" ++ x) ++ "c"` is
`("ab" ++ x) ++ "c"`, `LeanScript.Term.Optimize.StringAppend`).

Around the join points written at their jumps (`Term.joinCtor`, run between two passes of it),
the shared conditionals and the tests that only pick a jump argument (`Term.condJump`,
`LeanScript.Term.Optimize.CondJump`): `let x := share (c ? a : b); body`, where `x` is used once or
only as the operand of union case analyses, is `body[x := c ? a : b]` (each `case` of it is then a
case of a conditional of constructors, which `Term.joinCtor` makes an `if`); `if c then jump j a
else jump j b` is `jump j (c ? a : b)`; and `join j x := body; jump j a` is `body[x := a]`.  So
`let o := if c then some v else none; … o.get! … o.get! …` builds no option.

Then the loops whose state is always the same constructor (`Term.loopYield`,
`LeanScript.Term.Optimize.LoopYield`): when the initial state of a `nat_rec` is a literal `C a`
of a constructor with one field, the step takes the state apart and the arm of `C` answers
`C e` on every path, the loop is written over the field of `C` (`let y := nat_rec n a step';
rest[x := C y]`, the case analyses of `x` in `rest` reduced).  This is the `ForInStep` of a
`for` loop without `break`: its state becomes the mutable variables themselves.

Then the delays that only force another delay (`Term.delayEta`,
`LeanScript.Term.Optimize.DelayEta`): a known `val k := lazy (let x := e (); ret x)` (or the same
`thunk` around `force e`) is `e` itself, which replaces every mention of `k` (so
`fun f => (() => f())` is `fun f => f`).

Then the inlining in tail position (`Term.inlineRet`, `LeanScript.Term.Optimize.InlineRet`):
`let y := k a; ret y` is `ret e[a]` for a known closure computing `e`, whatever `e[a]` is,
dead bindings are dropped even when this changes the level (inside closed bodies), and a
known closure used once, whose closed body makes no call, is inlined at a call
(`Term.blockLetE`): its body, re-levelled (`Term.relvl`), replaces the call, its answer bound
to the call's result (`Term.bindRet`; when the body ends in a branch, the rest of the statement
becomes a join point the arms of the branch jump to).  The argument may be any pure expression,
a record literal included (`BlockFn.applyP`: the parameter is substituted by `Term.subst`,
which also reduces a case analysis of the literal; `Term.blockLetS` first names by `let` the
fields of the literal that compute something, `Args.shareFirst`, so that they are not
repeated).  A known closure used once whose closed body makes calls is inlined at its only
call when that call is reached through `let`s, record case analyses, `if` arms and join points
(`Term.inlineAt`).

Then the chains of additions and multiplications (`Term.arithWalk`,
`LeanScript.Term.Optimize.Arith`) of `Int`, `Nat` and the fixed-width integers: the literals
of a chain are folded into one (dropped when it is the unit), the copies of an unknown in a sum
are counted (`x + x + x` is `x * 3`), so are three copies or more in a product of `Int`s or
`Nat`s (`x * x * x` is `x ^ 3`), and the operands are combined from the left, the literal last
(`1 + (2 + (x + (x + 3))) + 4` is `x * 2 + 10`).

(`Term.simp` is kept separate: each of its rewrites is a step of the rewriting system of
`LeanScript.Term.Rewrite`, `Term.simp_star`.)

Except in `Term.inlineRet` (whose walk lets the level change), each rewrite is done only when
it keeps the level index of the statement (like the drops of `Term.dce`), which is decided on
the spot; otherwise the statement is kept as it is.
Last, `Term.dce` drops the dead bindings and counts the usages again, the fields of case
analyses included (a field that is never read is annotated `0`).
Then a computation used once is moved down past the `let`s that follow it and do not read it
(`Term.sinkWalk`, `LeanScript.Term.Optimize.SinkLet`): `let x [1] := f 1; let y [ω] := f 2;
ret ⟨x, y, y⟩` is `let y [ω] := f 2; let x [1] := f 1; ret ⟨x, y, y⟩`, so that the JavaScript
printer can write `f(1)` at its use; and a computation in front of an `if` that only one arm
reads is moved into that arm (`Term.sinkArm`).

`Term.optimizeN k` runs `optimize` `k` times (a rewrite can expose another one).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The rewrites, one step each -/

/-- The neutral expression `n` for the innermost unknown `x`, when the expression is `x`
    itself (and `none` otherwise).  `n` must have the level of `x`. -/
def Neu.substHead {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {d ℓ : Nat}
    (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) :
    {τ : Ty ks} → {ℓ' : Nat} → Neu Δ Φ (⟨σ, u, d⟩ :: Γ) τ ℓ' → Option (Neu Δ Φ Γ τ ℓ')
  | _, _, .var (.head _) => some (hl ▸ n)
  | _, _, .var (.tail _) => none
  | _, _, .data_out _ _ _ => none
  | _, _, .cond _ _ _ => none
  | _, _, .extern _ _ _ => none

/-- `Neu.substHead`, on a pure expression. -/
def PExpr.substHead {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {d ℓ : Nat}
    (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) :
    {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) τ o → Option (PExpr Δ Φ Γ τ o)
  | _, _, .neu m => (Neu.substHead n hl m).map .neu
  | _, _, .kvar _ => none
  | _, _, .lit _ _ => none
  | _, _, .enum_mk _ _ => none
  | _, _, .record_mk _ => none
  | _, _, .union_mk _ _ => none
  | _, _, .array_mk _ => none
  | _, _, .list_mk _ => none
  | _, _, .data_in _ _ _ => none

/-- `let x := share n; b` when `b` is `ret x` or `jump j x` (and `n` has the level of `x`):
    the answer is `n` itself. -/
def Term.shareTail {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  if hl : ℓ = d then
    match b with
    | .ret e =>
        match PExpr.substHead n hl e with
        | some e' =>
            if ho : o' = some (Lvl.meetL ℓ o') then (Term.ret e').castLvl ho
            else .letE u (.share n) (.ret e)
        | none => .letE u (.share n) (.ret e)
    | .jump j e =>
        match PExpr.substHead n hl e with
        | some e' =>
            if ho : o' = some (Lvl.meetL ℓ o') then (Term.jump j e').castLvl ho
            else .letE u (.share n) (.jump j e)
        | none => .letE u (.share n) (.jump j e)
    | .letV x v b => .letE u (.share n) (.letV x v b)
    | .letE x c b => .letE u (.share n) (.letE x c b)
    | .record_casesOn us m b => .letE u (.share n) (.record_casesOn us m b)
    | .branch br => .letE u (.share n) (.branch br)
  else .letE u (.share n) b

/-- `let x := share n; b`: copy propagation when `n` is an unknown of level `d`, otherwise
    `Term.shareTail`. -/
def Term.shareLet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  match n with
  | .var x =>
      if hl : ℓ = d then
        match b.rename KRen.id (URen.subst x hl) JRen.id with
        | some b' => if ho : o' = some (Lvl.meetL ℓ o') then b'.castLvl ho else Term.shareTail u n b
        | none => Term.shareTail u n b
      else Term.shareTail u n b
  | n => Term.shareTail u n b

/-- `let x := c; b`, with the rewrites of `share`. -/
def Term.mkLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  match c with
  | .share n => Term.shareLet u n b
  | c => .letE u c b

/-- `record_casesOn us n b`, dropped when `b` reads none of the fields. -/
def Term.mkRecordCasesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  match b.rename KRen.id (URen.dropN _) JRen.id with
  | some b' => if ho : o' = some (Lvl.meetL ℓ o') then b'.castLvl ho else .record_casesOn us n b
  | none => .record_casesOn us n b

/-! ## The walk -/

mutual
/-- Optimise the bodies inside a value. -/
def Val.simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.simp
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.simp
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.simp
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- Optimise a body. -/
def Body.simp : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.simp
  | _, _, _, _, _, _, .opened t h => .opened t.simp h
/-- Optimise the bodies inside a computation. -/
def Comp.simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.simp h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.simp h
  | _, _, _, _, _, .data_rec b ρ us brs j e h => .data_rec b ρ us (fun i => (brs i).simp) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).simp) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- Optimise a statement. -/
def Term.simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.simp b.simp
  | _, _, _, _, _, _, .letE u c b => Term.mkLetE u c.simp b.simp
  | _, _, _, _, _, _, .record_casesOn us n b => Term.mkRecordCasesOn us n b.simp
  | _, _, _, _, _, _, .branch br => .branch br.simp
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- Optimise a branch. -/
def Branch.simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.simp e.simp
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).simp)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.simp
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.simp main.simp
/-- Optimise the branches of a union's case analysis. -/
def Branches.simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.simp b₂.simp
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.simp bs.simp
end


/-! ## The second walk: sharing, identical branches, trivial join points -/

mutual
/-- `Term.cseWalk` inside the bodies of a value. -/
def Val.cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.cseWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.cseWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.cseWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.cseWalk` in a body. -/
def Body.cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.cseWalk
  | _, _, _, _, _, _, .opened t h => .opened t.cseWalk h
/-- `Term.cseWalk` inside the bodies of a computation. -/
def Comp.cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.cseWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.cseWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h => .data_rec b ρ us (fun i => (brs i).cseWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).cseWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **The second walk** of the optimiser: bottom-up, common subexpression elimination
    (`Term.cseLetE`), identical branches (`Term.mkBranch`) and trivial join points
    (`Branch.mkJoin`). -/
def Term.cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.cseWalk b.cseWalk
  | _, _, _, _, _, _, .letE u c b => Term.cseLetE u c.cseWalk b.cseWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.cseWalk
  | _, _, _, _, _, _, .branch br => Term.mkBranch br.cseWalk
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.cseWalk` in a branch. -/
def Branch.cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.cseWalk e.cseWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).cseWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.cseWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => Branch.mkJoin σ u uₓ body.cseWalk main.cseWalk
/-- `Term.cseWalk` in the branches of a union's case analysis. -/
def Branches.cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.cseWalk b₂.cseWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.cseWalk bs.cseWalk
end

mutual
theorem Val.cseWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → v.cseWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.cseWalk, Val.eval]; funext x; rw [Body.cseWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.cseWalk, Val.eval]; rw [Body.cseWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.cseWalk, Val.eval]; rw [Body.cseWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.cseWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.cseWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.cseWalk, Body.eval]; exact Term.cseWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.cseWalk, Body.eval]; exact Term.cseWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.cseWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.cseWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.cseWalk, Comp.eval]
      congr 1; funext k acc; exact Body.cseWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.cseWalk, Comp.eval]
      congr 1; funext acc x; exact Body.cseWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.cseWalk, Comp.eval]
      congr 1; funext i x; exact Body.cseWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.cseWalk, Comp.eval]
      congr 1; funext i x; exact Body.cseWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.cseWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.cseWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.cseWalk, Term.eval, Val.cseWalk_eval v, Term.cseWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.cseWalk]
      rw [Term.cseLetE_eval]
      simp only [Term.eval, Comp.cseWalk_eval c, Term.cseWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.cseWalk, Term.eval, Term.cseWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.cseWalk]
      rw [Term.mkBranch_eval]
      simp only [Term.eval, Branch.cseWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.cseWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.cseWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.cseWalk, Branch.eval, Term.cseWalk_eval t, Term.cseWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.cseWalk, Branch.eval]; exact Term.cseWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.cseWalk, Branch.eval]; exact Branches.cseWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.cseWalk]
      rw [Branch.mkJoin_eval]
      simp only [Branch.eval, Branch.cseWalk_eval main, Term.cseWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.cseWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.cseWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.cseWalk, Branches.eval, Term.cseWalk_eval b₁, Term.cseWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.cseWalk, Branches.eval, Term.cseWalk_eval b, Branches.cseWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-- **The optimiser**: the inlining of known closures that compute an expression
    (`Term.inlineKnown`), the rewrites of `Term.simp`, the known fields (`Term.widenFields`,
    then `Term.reuseFields`), the tests whose answer is already known dropped
    (`Term.knownTests`), the known sizes of array literals and the tests and join points
    they decide (`Term.knownSizes`), the tests shared by both arms of an `if` made first
    (`Term.shareTestWalk`), a test pushed into the answers when both arms of an `if` make the
    same other tests (`Term.zipTestWalk`), those of `Term.cseWalk`, the hoisting of the extern calls every
    path computes (`Term.hoistWalk`), the boolean conditions
    (`Term.condWalk`), two tests that end in the same answer merged into one condition
    (`Term.mergeTestWalk`), the known constant literals written in place in append chains
    (`Term.knownLits`), the append chains (`Term.appendWalk`), the join points written at their
    jumps (`Term.joinCtor`) between two passes of the shared conditionals written at their case
    analyses (`Term.condJump`), the loops whose state is always the same constructor written over
    its field (`Term.loopYield`), the delays that only force another
    delay replaced by it (`Term.delayEta`), the inlining in tail position with dead bindings dropped even when the
    level changes (`Term.inlineRet`), the chains of additions and multiplications
    (`Term.arithWalk`), then dead-code elimination, and last the computations used once moved
    down to their uses (`Term.sinkWalk`, on the usages that dead-code elimination has just
    counted). -/
def Term.optimize {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall.delayEta.inlineRet.arithWalk.dce.sinkWalk

/-- The optimiser, run `k` times. -/
def Term.optimizeN {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Nat → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | 0, t => t
  | k + 1, t => Term.optimizeN k t.optimize

/-! ## The rewrites preserve the value -/

theorem Neu.substHead_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {d ℓ : Nat}
    (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) {τ : Ty ks} {ℓ' : Nat}
    (m : Neu Δ Φ (⟨σ, u, d⟩ :: Γ) τ ℓ') {m' : Neu Δ Φ Γ τ ℓ'} (h : Neu.substHead n hl m = some m')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : m'.eval κ ρ = m.eval κ (Tuple.cons (n.eval κ ρ) ρ) := by
  subst hl
  cases m with
  | var x =>
      cases x with
      | head _ =>
          simp only [Neu.substHead, Option.some.injEq] at h
          subst h; simp [Neu.eval]
      | tail _ => simp [Neu.substHead] at h
  | data_out => simp [Neu.substHead] at h
  | cond => simp [Neu.substHead] at h
  | extern => simp [Neu.substHead] at h

theorem PExpr.substHead_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {d ℓ : Nat}
    (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) τ o) {e' : PExpr Δ Φ Γ τ o} (h : PExpr.substHead n hl e = some e')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : e'.eval κ ρ = e.eval κ (Tuple.cons (n.eval κ ρ) ρ) := by
  cases e with
  | neu m =>
      simp only [PExpr.substHead, Option.map_eq_some_iff] at h
      obtain ⟨m', hm, rfl⟩ := h
      simp only [PExpr.eval]
      exact Neu.substHead_eval n hl m hm κ ρ
  | _ => simp [PExpr.substHead] at h

theorem Term.shareTail_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Term.shareTail u n b).eval κ ρ jκ = (Term.letE u (.share n) b).eval κ ρ jκ := by
  unfold Term.shareTail
  split
  · rename_i hl
    split
    · rename_i e
      split
      · rename_i e' he
        split
        · rw [Term.eval_castLvl]
          simp only [Term.eval, Comp.eval]
          exact PExpr.substHead_eval n hl e he κ ρ
        · rfl
      · rfl
    · rename_i j e
      split
      · rename_i e' he
        split
        · rw [Term.eval_castLvl]
          simp only [Term.eval, Comp.eval]
          rw [PExpr.substHead_eval n hl e he κ ρ]
        · rfl
      · rfl
    all_goals rfl
  · rfl

theorem Term.shareLet_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Term.shareLet u n b).eval κ ρ jκ = (Term.letE u (.share n) b).eval κ ρ jκ := by
  unfold Term.shareLet
  split
  · split
    · rename_i x hl
      split
      · rename_i b' hb
        split
        · rw [Term.eval_castLvl, Term.rename_eval (KRen.Agree.id _) (URen.Agree.subst x hl ρ)
            (JRen.Agree.id _) b hb]
          simp [Term.eval, Comp.eval, Neu.eval]
        · exact Term.shareTail_eval u _ b κ ρ jκ
      · exact Term.shareTail_eval u _ b κ ρ jκ
    · exact Term.shareTail_eval u _ b κ ρ jκ
  · exact Term.shareTail_eval u _ b κ ρ jκ

theorem Term.mkLetE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Term.mkLetE u c b).eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  unfold Term.mkLetE
  split
  · exact Term.shareLet_eval u _ b κ ρ jκ
  · rfl

theorem Term.mkRecordCasesOn_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.mkRecordCasesOn us n b).eval κ ρ jκ = (Term.record_casesOn us n b).eval κ ρ jκ := by
  unfold Term.mkRecordCasesOn
  split
  · rename_i b' hb
    split
    · rw [Term.eval_castLvl]
      simp only [Term.eval]
      exact Term.rename_eval (KRen.Agree.id _) (URen.Agree.dropN ρ _ _) (JRen.Agree.id _) b hb
    · rfl
  · rfl

/-! ## The optimiser preserves the value -/

mutual
theorem Val.simp_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → v.simp.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.simp, Val.eval]; funext x; rw [Body.simp_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.simp, Val.eval]; rw [Body.simp_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.simp, Val.eval]; rw [Body.simp_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.simp_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.simp.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.simp, Body.eval]; exact Term.simp_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.simp, Body.eval]; exact Term.simp_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.simp_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.simp.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.simp, Comp.eval]
      congr 1; funext k acc; exact Body.simp_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.simp, Comp.eval]
      congr 1; funext acc x; exact Body.simp_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.simp, Comp.eval]
      congr 1; funext i x; exact Body.simp_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.simp, Comp.eval]
      congr 1; funext i x; exact Body.simp_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.simp_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.simp.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.simp, Term.eval, Val.simp_eval v, Term.simp_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.simp]
      rw [Term.mkLetE_eval]
      simp only [Term.eval, Comp.simp_eval c, Term.simp_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.simp]
      rw [Term.mkRecordCasesOn_eval]
      simp only [Term.eval, Term.simp_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.simp, Term.eval, Branch.simp_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.simp_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.simp.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.simp, Branch.eval, Term.simp_eval t, Term.simp_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.simp, Branch.eval]; exact Term.simp_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.simp, Branch.eval]; exact Branches.simp_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.simp, Branch.eval, Branch.simp_eval main, Term.simp_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.simp_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.simp.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.simp, Branches.eval, Term.simp_eval b₁, Term.simp_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.simp, Branches.eval, Term.simp_eval b, Branches.simp_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-- **The optimiser does not change the value of a statement**, in any environment. -/
theorem Term.optimize_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.optimize.eval κ ρ jκ = t.eval κ ρ jκ := by
  rw [Term.optimize, Term.sinkWalk_eval, Term.dce_eval, Term.arithWalk_eval, Term.inlineRet_eval, Term.delayEta_eval, Term.openCall_eval, Term.loopYield_eval, Term.condJump_eval, Term.joinCtor_eval, Term.condJump_eval, Term.appendWalk_eval, Term.knownLits_eval, Term.mergeTestWalk_eval, Term.condWalk_eval,
    Term.hoistWalk_eval, Term.cseWalk_eval, Term.dce_eval, Term.zipTestWalk_eval, Term.shareTestWalk_eval, Term.knownSizes_eval, Term.knownTests_eval,
    Term.reuseFields_eval _ [] _ _ _ (fun _ h => nomatch h), Term.widenFields_eval,
    Term.simp_eval, Term.inlineKnown_eval]

/-- Running the optimiser any number of times does not change the value either. -/
theorem Term.optimizeN_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} : (k : Nat) → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (jκ : JEnv Δ τ js) → (t.optimizeN k).eval κ ρ jκ = t.eval κ ρ jκ
  | 0, _, _, _, _ => rfl
  | k + 1, t, κ, ρ, jκ => by
      rw [Term.optimizeN, Term.optimizeN_eval k, Term.optimize_eval]

/-- **The optimiser does not change the result of a program.** -/
theorem Term.optimize_run {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) :
    t.optimize.run = t.run :=
  t.optimize_eval _ _ _

/-- The same for the optimiser run `k` times. -/
theorem Term.optimizeN_run {τ : Ty ks} {o : Lvl} (k : Nat) (t : Term Δ 0 [] [] τ [] o) :
    (t.optimizeN k).run = t.run :=
  t.optimizeN_eval k _ _ _

end LeanScript

end
