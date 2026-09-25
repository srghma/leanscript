module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# Three more redexes: known case on numbers and primitives, known case through a `let`,
# and a delay of a force

* **Case of a known number or primitive, on a variable.**  A dispatch on a natural number
  (zero or successor), an integer (`ofNat` or `negSucc`) or a primitive with one
  constructor (`UInt8`, `Char`, a float, …) inside a branch of a dispatch on the same
  variable is a redex: in that branch the constructor is known and its fields are bound.
  `Term.nat_casesOn`, `Term.int_casesOn` and the one-branch primitive dispatches now count
  their scrutinee (`Usage.scrutinize`) and ask that their branches do not take it apart
  again (`hKnown`), as the dispatches on datatypes already did.
* **Case of a constructor bound by a `let`.**  `let p = (a, b); … match p …`: the
  dispatch is a redex, since `p` is known to be the pair.  `Term.letE` asks that a `let`
  of a constructor is not taken apart in its body (`hKnownLet`, `Head.letKnown`); the
  translation binds the fields instead, `let a' = a; let b' = b; …`, and each dispatch
  reads them.
* **A delay of a force of a name.**  `Thunk.mk (fun _ => t.get)` is `t`, and a delay of
  `l ()` is `l`.  A force records whether it forces a name (`Head.force`), and
  `Term.thunk_mk` and `Term.lazy_mk` ask that they do not delay such a force (`hEta`).  A
  force of a computation is left alone: delaying it defers the computation.

Each translation is checked against the Lean function by `rfl`, and its shape by a
printed snapshot.
-/

namespace TermTests.MoreRedexes

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)


/-- The schema of a record of two naturals, for terms written by hand. -/
def pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

/-- A record of two naturals. -/
abbrev pairRec : TyWf := TyWf.record pairSchema

/-- The schema of a record of two such records. -/
def pairPairSchema : LeanRecordSchema TyWf := ⟨pairRec, pairRec, []⟩

/-! ## Written by hand: what the grammar accepts and rejects -/

-- `fun n => match n with | 0 => 1 | k + 1 => match n with | 0 => 5 | j + 1 => j`: in the
-- successor branch, `n` is known to be `k + 1`.
/--
error: could not synthesize default value for parameter 'hKnown' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).rescrutinizes
      (0 +
        (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail))
            (Usage.single DeBruijn.head.tail + Usage.cond 0 + (Usage.single DeBruijn.head).tail.cond)).tail) =
    false
is false
-/
#guard_msgs (error) in
def natNatSame :=
  (.lam (.nat_casesOn (.var (v♯0)) (.nat_mk 1)
    (.nat_casesOn (.var (v♯1)) (.nat_mk 5) (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun n m => match n with | 0 => 1 | k + 1 => match m with | 0 => 5 | j + 1 => j`: the
    inner dispatch is on another variable, a term. -/
def natNatOther :=
  (.lam (.lam (.nat_casesOn (.var (v♯1)) (.nat_mk 1)
    (.nat_casesOn (.var (v♯1)) (.nat_mk 5) (.var (v♯0))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run natNatOther 3 4 = 3 := rfl

-- `fun i => match i with | .ofNat n => (match i with | .ofNat m => m | .negSucc m => m)
-- | .negSucc n => n`: in the `ofNat` branch, `i` is known.
/--
error: could not synthesize default value for parameter 'hKnown' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).rescrutinizes
      ((Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail))
            (Usage.single DeBruijn.head.tail + (Usage.single DeBruijn.head).tail.cond +
              (Usage.single DeBruijn.head).tail.cond)).tail +
        (Usage.single DeBruijn.head).tail) =
    false
is false
-/
#guard_msgs (error) in
def intIntSame :=
  (.lam (.int_casesOn (.var (v♯0))
    (.int_casesOn (.var (v♯1)) (.var (v♯0)) (.var (v♯0))) (.var (v♯0))) :
    Term sig0 [] _ (TyWf.prim .int ⇒ TyWf.prim .nat) .lam)

-- `fun c => match c with | ⟨v⟩ => match c with | ⟨w⟩ => w + v` (code points, as
-- `UInt32`): in the branch, `c` is known to be `⟨v⟩`.
/--
error: could not synthesize default value for parameter 'hKnown' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).rescrutinizes
      (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail))
          (Usage.single DeBruijn.head.tail +
            (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
                (Usage.arg (Head.var (Var.index DeBruijn.head.tail)) (Usage.single DeBruijn.head.tail) +
                  0)).tail)).tail =
    false
is false
-/
#guard_msgs (error) in
def charCharSame :=
  (.lam (.char_casesOn (.var (v♯0)) (.char_casesOn (.var (v♯1))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
      fun vs => .lean_uint32_add vs.1 vs.2.1))) :
    Term sig0 [] _ (TyWf.prim .char ⇒ TyWf.prim .uint32) .lam)

/-- `fun c => match c with | ⟨v⟩ => v + v`: the known-case form, a term. -/
def charOnce :=
  (.lam (.char_casesOn (.var (v♯0))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .lean_uint32_add vs.1 vs.2.1)) :
    Term sig0 [] _ (TyWf.prim .char ⇒ TyWf.prim .uint32) .lam)

example : run charOnce 'a' = 194 := rfl

-- `fun n => let p = (n * n, n + 1); (match p with | (a, _) => a) + (match p with
-- | (_, b) => b)`: `p` is known to be the pair.
/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.allAtom [Head.comp, Head.comp] = true
is false
---
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.allAtom
      [(Head.var (Var.index DeBruijn.head)).join Head.empty,
        (Head.var (Var.index DeBruijn.head.tail)).join Head.empty] =
    true
is false
---
error: could not synthesize default value for parameter 'hKnownLet' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.ctorOf [Head.comp, Head.comp]).letKnown (TyWf.record pairSchema)
      (Usage.arg ((Head.var (Var.index DeBruijn.head)).join Head.empty)
          (Usage.scrutinize (Head.var (Var.index DeBruijn.head))
            (Usage.single DeBruijn.head + Usage.drop pairSchema.toList (Usage.single DeBruijn.head))) +
        (Usage.arg ((Head.var (Var.index DeBruijn.head.tail)).join Head.empty)
            (Usage.scrutinize (Head.var (Var.index DeBruijn.head))
              (Usage.single DeBruijn.head + Usage.drop pairSchema.toList (Usage.single DeBruijn.head.tail))) +
          0)) =
    false
is false
---
error: Compilation failed, locally inferred compilation type
  ℕ × ℕ × PUnit.{1}
differs from type
  lcAny × lcAny × PUnit.{1}
that would be inferred in other modules. This usually means that a type `def` involved with the mentioned declarations needs to be `@[expose]`d. This is a current compiler limitation for `module`s that may be lifted in the future.
-/
#guard_msgs (error) in
def letPairTakenApart :=
  (.lam (.letE
    (.record_mk pairSchema
      (.cons (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
          fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
        (.cons (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 1) .nil))
          fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) .nil)))
    (.externCall
      (.cons (.record_casesOn (.var (v♯0)) (.var (v♯0)))
        (.cons (.record_casesOn (.var (v♯0)) (.var (v♯1))) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun n => let a = n * n; let b = n + 1; let c = a + b; c + a`: the fields bound (and,
    in A-normal form, every operand an atom), a term. -/
def letFieldsBound :=
  (.lam (.letE
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
    (.letE (.externCall (.cons (.var (v♯1)) (.cons (.nat_mk 1) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.letE (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯2)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run letFieldsBound 3 = 22 := rfl

/-- `fun n => let a = n * n; let b = n + 1; let p = (a, b); (p, p)`: a `let` of a
    constructor that is shared but not taken apart, a term (its fields are atoms, so they
    are bound first). -/
def letPairShared :=
  (.lam (.letE (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
          fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
    (.letE (.externCall (.cons (.var (v♯1)) (.cons (.nat_mk 1) .nil))
          fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.letE (.record_mk pairSchema (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil)))
    (.record_mk pairPairSchema (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil)))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.record pairPairSchema) .lam)

-- `fun t => Thunk.mk (fun _ => t.get)`: that is `t`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.isForcedName true (Head.force true (Head.var (Var.index DeBruijn.head)).isName) = false
is false
-/
#guard_msgs (error) in
def thunkOfForce :=
  (.lam (.thunk_mk (.thunk_force (.var (v♯0)))) :
    Term sig0 [] _ (.thunk (TyWf.prim .nat) ⇒ .thunk (TyWf.prim .nat)) .lam)

-- `fun l => (fun _ => l ())`, with the unit erased: that is `l`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.isForcedName false (Head.force false (Head.var (Var.index DeBruijn.head)).isName) = false
is false
-/
#guard_msgs (error) in
def lazyOfForce :=
  (.lam (.lazy_mk (.lazy_force (.var (v♯0)))) :
    Term sig0 [] _ (.lazy (TyWf.prim .nat) ⇒ .lazy (TyWf.prim .nat)) .lam)

/-- `fun f n => Thunk.mk (fun _ => let t = f n; t.get)`: what is forced is a computation,
    which the delay defers — a term (in A-normal form the computation is bound, and its
    variable forced). -/
def thunkOfForcedCall :=
  (.lam (.lam (.thunk_mk (.letE (.ap (.var (v♯1)) (.var (v♯0))) (.thunk_force (.var (v♯0)))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ .thunk (TyWf.prim .nat)) ⇒ TyWf.prim .nat ⇒ .thunk (TyWf.prim .nat)) .lam)

example : run thunkOfForcedCall (fun n => n + 1) 4 = 5 := rfl

/-! ## Written by hand, then optimized: `#leanscript_optimize`

The Lean programs above do not produce a dispatch on an integer or on a character (the
translation takes those apart with externs), so the known case on them is exercised on
terms written by hand: the redexes rejected above, optimized, are the terms accepted
above. -/

example : (#leanscript_optimize (.lam (.char_casesOn (.var (v♯0)) (.char_casesOn (.var (v♯1))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
      fun vs => .lean_uint32_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .char ⇒ TyWf.prim .uint32) _) = charOnce := rfl

/-- The `int` redex above, optimized: `fun i => match i with | .ofNat n => n
    | .negSucc n => n`. -/
example : (#leanscript_optimize (.lam (.int_casesOn (.var (v♯0))
    (.int_casesOn (.var (v♯1)) (.var (v♯0)) (.var (v♯0))) (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .int ⇒ TyWf.prim .nat) _) =
  .lam (.int_casesOn (.var (v♯0)) (.var (v♯0)) (.var (v♯0))) := rfl

/-- The `nat` redex above, optimized: `fun n => match n with | 0 => 1 | k + 1 => k`. -/
example : (#leanscript_optimize (.lam (.nat_casesOn (.var (v♯0)) (.nat_mk 1)
    (.nat_casesOn (.var (v♯1)) (.nat_mk 5) (.var (v♯0))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _) =
  .lam (.nat_casesOn (.var (v♯0)) (.nat_mk 1) (.var (v♯0))) := rfl

/-- The re-delayed forces above, optimized: the identity. -/
example : (#leanscript_optimize (.lam (.lazy_mk (.lazy_force (.var (v♯0))))) :
    Term sig0 [] _ (.lazy (TyWf.prim .nat) ⇒ .lazy (TyWf.prim .nat)) _) = .lam (.var (v♯0)) :=
  rfl

/-- The `let` of a pair taken apart, optimized: the fields bound, the pair gone. -/
example : (#leanscript_optimize (.lam (.letE
    (.record_mk pairSchema
      (.cons (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
          fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
        (.cons (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 1) .nil))
          fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) .nil)))
    (.externCall
      (.cons (.record_casesOn (.var (v♯0)) (.var (v♯0)))
        (.cons (.record_casesOn (.var (v♯0)) (.var (v♯1))) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _) =
  .lam (.letE (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
    (.letE (.externCall (.cons (.var (v♯1)) (.cons (.nat_mk 1) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) := rfl

/-! ## Translated: what `#leanscript_to_term` emits -/

/-- `match n with | 0 => 1 | k + 1 => (match n with | 0 => 5 | j + 1 => j) + k` is
    `match n with | 0 => 1 | k + 1 => k + k`. -/
def natTwice (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => (match n with | 0 => 5 | j + 1 => j) + k

def natTwice_term := (#leanscript_to_term natTwice : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run natTwice_term 0 = 1 := rfl
example : run natTwice_term 4 = 6 := rfl

/--
info: ((Term.var DeBruijnProj.head).nat_casesOn (Term.nat_mk 1)
      (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯)
      ⋯ ⋯ ⋯ natTwice_term._proof_8).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) natTwice_term

/-- In the zero branch, `n` is known to be `0`:
    `match n with | 0 => (match n with | 0 => 7 | _ + 1 => 8) | k + 1 => k` is
    `match n with | 0 => 7 | k + 1 => k`. -/
def natZeroTwice (n : Nat) : Nat :=
  match n with
  | 0 => (match n with | 0 => 7 | _ + 1 => 8)
  | k + 1 => k

def natZeroTwice_term := (#leanscript_to_term natZeroTwice : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run natZeroTwice_term 0 = 7 := rfl
example : run natZeroTwice_term 5 = 4 := rfl

/--
info: ((Term.var DeBruijnProj.head).nat_casesOn (Term.nat_mk 7) (Term.var DeBruijnProj.head) ⋯ ⋯ ⋯ ⋯).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) natZeroTwice_term

/-- `let p := (n * n, n + 1); p.1 + p.2 + p.1` is `let a := n * n; a + (n + 1) + a`: the
    fields are bound, `b` is read once and inlined, and `p` is gone. -/
def letPair (n : Nat) : Nat :=
  let p := (n * n, n + 1)
  p.1 + p.2 + p.1

def letPair_term := (#leanscript_to_term letPair : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run letPair_term 3 = 22 := rfl

/--
info: ((Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
          (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
      ((Term.externCall (Spine.cons (Term.var DeBruijnProj.head.tail) (Spine.cons (Term.nat_mk 1) Spine.nil))
            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
        ((Term.externCall
              (Spine.cons (Term.var DeBruijnProj.head.tail) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
              (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
          (Term.externCall
            (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head.tail.tail) Spine.nil))
            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯)
          letPair_term._proof_13 ⋯ ⋯ ⋯ ⋯)
        letPair_term._proof_13 ⋯ ⋯ ⋯ ⋯)
      letPair_term._proof_13 ⋯ ⋯ ⋯ ⋯).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) letPair_term

/-- `let p := (n * n, n + 1); (p.1 + p.2, p)`: the pair is still built once, on the bound
    fields, and the projections read the fields. -/
def letPairKeep (n : Nat) : Nat × (Nat × Nat) :=
  let p := (n * n, n + 1)
  (p.1 + p.2, p)

def letPairKeep_term :=
  (#leanscript_to_term letPairKeep : Term sig0 [] _ (TyWf.prim .nat ⇒ tyWfOf (Nat × (Nat × Nat))) .lam)

/--
info: ((Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
          (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
      ((Term.externCall (Spine.cons (Term.var DeBruijnProj.head.tail) (Spine.cons (Term.nat_mk 1) Spine.nil))
            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
        ((Term.record_mk
              { fst := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := natTwice_term._proof_1 },
                snd := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := natTwice_term._proof_1 }, rest := [] }
              (Spine.cons (Term.var DeBruijnProj.head.tail) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil)) ⋯).letE
          ((Term.externCall
                (Spine.cons (Term.var DeBruijnProj.head.tail.tail)
                  (Spine.cons (Term.var DeBruijnProj.head.tail) Spine.nil))
                (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
            (Term.record_mk
              { fst := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := natTwice_term._proof_1 },
                snd :=
                  {
                    toTy :=
                      Ty.shape
                        (TyShape.record
                          { fst := Ty.shape (TyShape.prim LeanPrimTy.nat),
                            snd := Ty.shape (TyShape.prim LeanPrimTy.nat), rest := [] }),
                    isWf := letPairKeep_term._proof_2 },
                rest := [] }
              (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head.tail) Spine.nil)) ⋯)
            letPair_term._proof_13 ⋯ ⋯ ⋯ ⋯)
          ⋯ ⋯ ⋯ ⋯ ⋯)
        letPair_term._proof_13 ⋯ ⋯ ⋯ ⋯)
      letPair_term._proof_13 ⋯ ⋯ ⋯ ⋯).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) letPairKeep_term

/-- `Thunk.mk (fun _ => t.get)` is `t`. -/
def thunkEta (t : Thunk Nat) : Thunk Nat := Thunk.mk (fun _ => t.get)

def thunkEta_term :=
  (#leanscript_to_term thunkEta : Term sig0 [] _ (.thunk (TyWf.prim .nat) ⇒ .thunk (TyWf.prim .nat)) .lam)

/--
info: (Term.var DeBruijnProj.head).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) thunkEta_term

end TermTests.MoreRedexes
