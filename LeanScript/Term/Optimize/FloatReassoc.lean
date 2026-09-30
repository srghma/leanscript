module

public import LeanScript.Term.Optimize.Append

@[expose] public section

set_option autoImplicit false

/-!
# Re-associating float chains (opt-in, **not** value-preserving)

`Term.floatReassoc` regroups every chain of `Float` (`Float32`) additions, and every chain of
multiplications, **from the left**, and folds the literals that are *neighbours* in the chain
(in the order of the chain; nothing is reordered):

    1.0 + (((((2.0 + x) + x) + x) + x) + 3.0) + 4.0   ~>   3.0 + x + x + x + x + 7.0

which is what the legacy backend (`purescript-backend-optimizer`) does to `Number` chains
(`Tests/SnapshotsPBOPure/legacy-backend/AssocNumberOps.js`).

IEEE addition and multiplication are **not associative**, so this pass **changes results**:
at `x = 3/7` the two sides above differ in the last bit (proved in
`Tests/TermTests/Optimize/AssocNumberOpsTest.lean`).  It is therefore *not* part of
`Term.optimize` (whose passes are all proved to preserve `Term.eval`) and has no preservation
theorem; the command line runs it only with `--float-reassoc`.  Chains of the other types are
left to `Term.arithWalk`, which normalises them exactly.
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks}

/-- The float operations whose chains are re-associated. -/
inductive FloatOp where
  | add64 | mul64 | add32 | mul32
  deriving DecidableEq, Repr

namespace FloatOp

/-- The type of the operands. -/
def prim : FloatOp → LeanPrimTy
  | .add64 | .mul64 => .float
  | .add32 | .mul32 => .float32

/-- The values of the operands. -/
abbrev D (a : FloatOp) : Type := a.prim.denote

/-- The operation on two literals, as the evaluator of its extern computes it. -/
def op : (a : FloatOp) → a.D → a.D → a.D
  | .add64 => fun x y => HashableFloat.normalize (Float.add x.toFloat y.toFloat)
  | .mul64 => fun x y => HashableFloat.normalize (Float.mul x.toFloat y.toFloat)
  | .add32 => fun x y => HashableFloat32.normalize (Float32.add x.toFloat32 y.toFloat32)
  | .mul32 => fun x y => HashableFloat32.normalize (Float32.mul x.toFloat32 y.toFloat32)

/-- The extern of the operation. -/
def ext : (a : FloatOp) → Extern ks [.prim a.prim, .prim a.prim] (.prim a.prim)
  | .add64 => .floatExtern .lean_float_add
  | .mul64 => .floatExtern .lean_float_mul
  | .add32 => .float32Extern .lean_float32_add
  | .mul32 => .float32Extern .lean_float32_mul

variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- An operand of a chain: a pure expression of the type, at any level. -/
abbrev Opnd (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) (a : FloatOp) : Type :=
  Σ o : Lvl, PExpr Δ Φ Γ (.prim a.prim) o

/-- The two operands, when a pure expression is a call of the operation. -/
def view : (a : FloatOp) → {o : Lvl} → PExpr Δ Φ Γ (.prim a.prim) o →
    Option (Opnd Δ Φ Γ a × Opnd Δ Φ Γ a)
  | .add64, _, .neu (.extern (.floatExtern .lean_float_add) (.cons x (.cons y .nil)) _) =>
      some (⟨_, x⟩, ⟨_, y⟩)
  | .mul64, _, .neu (.extern (.floatExtern .lean_float_mul) (.cons x (.cons y .nil)) _) =>
      some (⟨_, x⟩, ⟨_, y⟩)
  | .add32, _, .neu (.extern (.float32Extern .lean_float32_add) (.cons x (.cons y .nil)) _) =>
      some (⟨_, x⟩, ⟨_, y⟩)
  | .mul32, _, .neu (.extern (.float32Extern .lean_float32_mul) (.cons x (.cons y .nil)) _) =>
      some (⟨_, x⟩, ⟨_, y⟩)
  | _, _, _ => none

/-- The operands of a chain, left to right, however it is grouped (at most `n` levels deep). -/
def flat (a : FloatOp) : Nat → Opnd Δ Φ Γ a → List (Opnd Δ Φ Γ a)
  | 0, p => [p]
  | n + 1, p =>
    match a.view p.2 with
    | some (x, y) => flat a n x ++ flat a n y
    | none => [p]

/-- The value of an operand that is a literal. -/
def litVal? (a : FloatOp) : Opnd Δ Φ Γ a → Option a.D
  | ⟨_, .lit _ v⟩ => some v
  | _ => none

/-- Neighbouring literals folded, left to right (`acc` is the literal being built). -/
def foldRuns (a : FloatOp) : Option a.D → List (Opnd Δ Φ Γ a) → List (Opnd Δ Φ Γ a)
  | none, [] => []
  | some c, [] => [⟨none, .lit a.prim c⟩]
  | acc, p :: ps =>
    match a.litVal? p, acc with
    | some v, none => foldRuns a (some v) ps
    | some v, some c => foldRuns a (some (a.op c v)) ps
    | none, none => p :: foldRuns a none ps
    | none, some c => ⟨none, .lit a.prim c⟩ :: p :: foldRuns a none ps

/-- `x ∘ r`, when one at least is open. -/
def mkOp (a : FloatOp) (x r : Opnd Δ Φ Γ a) : Option (Opnd Δ Φ Γ a) :=
  match h : Lvl.meet x.1 r.1 with
  | some ℓ => some ⟨some ℓ, .neu (.extern a.ext (.cons x.2 (.cons r.2 .nil))
      (by rw [Lvl.meet_none]; exact h))⟩
  | none => none

/-- `((x₁ ∘ x₂) ∘ x₃) ∘ … ∘ xₙ`. -/
def build (a : FloatOp) : List (Opnd Δ Φ Γ a) → Option (Opnd Δ Φ Γ a)
  | [] => none
  | x :: xs => xs.foldlM (fun acc c => a.mkOp acc c) x

/-- How deep a chain is taken apart. -/
def flatFuel : Nat := 256

/-- A chain re-associated from the left, neighbouring literals folded, when the result is
    still a neutral expression of the same level (otherwise the expression is kept). -/
def reassoc (a : FloatOp) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim a.prim) ℓ) :
    Neu Δ Φ Γ (.prim a.prim) ℓ :=
  match a.build (a.foldRuns none (a.flat flatFuel ⟨_, .neu n⟩)) with
  | some ⟨o, p⟩ =>
    if h : o = some ℓ then
      match h ▸ p with
      | .neu m => m
      | _ => n
    else n
  | none => n

/-- `FloatOp.reassoc` at a leaf type, when it is the type of the operation. -/
def reassocAt (a : FloatOp) (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ) :
    Neu Δ Φ Γ (.prim p) ℓ :=
  if h : a.prim = p then h ▸ a.reassoc (h ▸ n) else n

end FloatOp

/-- `FloatOp.reassocAt` of the four operations on a neutral expression. -/
def Neu.floatReassocAt {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | .prim p, _, n => [FloatOp.add64, .mul64, .add32, .mul32].foldl (fun n a => a.reassocAt p n) n
  | _, _, n => n

mutual
/-- `Neu.floatReassocAt` at every extern call of a neutral expression, bottom-up. -/
def Neu.floatReassoc {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | _, _, .var x => .var x
  | _, _, .data_out b j e => .data_out b j e.floatReassoc
  | _, _, .cond c a b => .cond c.floatReassoc a.floatReassoc b.floatReassoc
  | _, _, .extern e args h => Neu.floatReassocAt (.extern e args.floatReassoc h)
/-- `Neu.floatReassoc` in a pure expression. -/
def PExpr.floatReassoc {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ o
  | _, _, .neu n => .neu n.floatReassoc
  | _, _, .kvar k => .kvar k
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk args.floatReassoc
  | _, _, .union_mk ix args => .union_mk ix args.floatReassoc
  | _, _, .array_mk es => .array_mk es.floatReassoc
  | _, _, .list_mk es => .list_mk es.floatReassoc
  | _, _, .data_in b j e => .data_in b j e.floatReassoc
/-- `Neu.floatReassoc` in arguments. -/
def Args.floatReassoc {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Args Δ Φ Γ σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons a.floatReassoc as.floatReassoc
/-- `Neu.floatReassoc` in the elements of a literal. -/
def Elems.floatReassoc {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → Elems Δ Φ Γ t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons e.floatReassoc es.floatReassoc
end

mutual
/-- `Term.floatReassoc` in a value. -/
def Val.floatReassoc : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.floatReassoc
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.floatReassoc
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.floatReassoc
  | _, _, _, _, _, .record_mk args => .record_mk args.floatReassoc
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args.floatReassoc
  | _, _, _, _, _, .array_mk es => .array_mk es.floatReassoc
  | _, _, _, _, _, .list_mk es => .list_mk es.floatReassoc
  | _, _, _, _, _, .data_in b j e => .data_in b j e.floatReassoc
/-- `Term.floatReassoc` in a body. -/
def Body.floatReassoc : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.floatReassoc
  | _, _, _, _, _, _, .opened t h => .opened t.floatReassoc h
/-- `Term.floatReassoc` in a computation. -/
def Comp.floatReassoc : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f.floatReassoc a.floatReassoc h
  | _, _, _, _, _, .share n => .share n.floatReassoc
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n.floatReassoc z.floatReassoc s.floatReassoc h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a.floatReassoc z.floatReassoc s.floatReassoc h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).floatReassoc) j e.floatReassoc h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).floatReassoc) j e.floatReassoc h
  | _, _, _, _, _, .thunk_force e => .thunk_force e.floatReassoc
  | _, _, _, _, _, .lazy_force e => .lazy_force e.floatReassoc
/-- **Float chains re-associated** everywhere in a statement (`Neu.floatReassocAt`), bottom-up.
    **Changes results**: see the module documentation. -/
def Term.floatReassoc : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e.floatReassoc
  | _, _, _, _, _, _, .letV u v b => .letV u v.floatReassoc b.floatReassoc
  | _, _, _, _, _, _, .letE u c b => .letE u c.floatReassoc b.floatReassoc
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n.floatReassoc b.floatReassoc
  | _, _, _, _, _, _, .branch br => .branch br.floatReassoc
  | _, _, _, _, _, _, .jump j e => .jump j e.floatReassoc
/-- `Term.floatReassoc` in a branch. -/
def Branch.floatReassoc : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c.floatReassoc t.floatReassoc e.floatReassoc
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e.floatReassoc (fun i => (bs i).floatReassoc)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e.floatReassoc bs.floatReassoc
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.floatReassoc main.floatReassoc
/-- `Term.floatReassoc` in the branches of a union's case analysis. -/
def Branches.floatReassoc : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.floatReassoc b₂.floatReassoc
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.floatReassoc bs.floatReassoc
end

end LeanScript

end
