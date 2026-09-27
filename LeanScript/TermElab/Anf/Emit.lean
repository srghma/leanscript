module

public import LeanScript.TermElab.Anf.Render

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Emitting bindings, returns, jumps and join points
-/

open Lean Meta Elab Term

namespace LeanScript.Anf

/-! ## Emitting -/

/-- `let x := c; …` of a computation of level `ℓ`. -/
def emitComp (cs : Lean.Term) (ℓ : Nat) (p : Pos) (k : Sem → Pos → TermElabM Out) :
    TermElabM Out := do
  let c := p.core
  let r ← k (.unk (.out c.du c.depth)) { p with core := { c with du := c.du + 1 } }
  return { stx := ← `(LeanScript.Term.letE (d := $(quote c.depth)) .many $cs $(r.stx)), lv := lmeet (some ℓ) r.lv }

/-- `val %k := v; …` of a value of level `o`, known as `mk` of its name afterwards. -/
def emitVal (vs : Lean.Term) (o : Lvl) (mk : KRef → Sem) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  let c := p.core
  let r ← k (mk { pos := c.dk, lv := o }) { p with core := { c with dk := c.dk + 1 } }
  return { stx := ← `(LeanScript.Term.letV .many $vs $(r.stx)), lv := lmeet o r.lv }

/-- The operand level of a computation, which must be open. -/
def openLv (o : Lvl) (what : String) : TermElabM Nat :=
  match o with
  | some ℓ => pure ℓ
  | none => throwError "internal error of the normaliser: {what} with no open operand"

/-- `return v`. -/
def retOut (s : Sem) (p : Pos) : TermElabM Out := do
  return { stx := ← `(LeanScript.Term.ret $(← render s p.core false)), lv := s.lv }

/-- Jump with `s` to the join point `id`: `Term.jump` when it is placed, its body (inlined)
    when it is pending. -/
def jumpTo (id : Name) (s : Sem) (p : Pos) : TermElabM Out := do
  let c := p.core
  if let some l := c.placed.lookup id then
    return { stx := ← `(LeanScript.Term.jump $(← jvarStx (c.jd - 1 - l)) $(← render s c false)),
             lv := s.lv }
  match p.pend.find? (·.id == id) with
  | some pj => pj.k s c
  | none => throwError "internal error of the normaliser: unknown join point"

/-- Give the value `s` to `K`. -/
def Kont.apply (K : Kont) (s : Sem) (p : Pos) : TermElabM Out :=
  match K with
  | .ret => retOut s p
  | .jump id => jumpTo id s p
  | .fn f => f s p

/-- The join points pending at `p` (not placed yet), outermost first. -/
def Pos.pending (p : Pos) : List Pend :=
  (p.pend.filter fun pj => (p.core.placed.lookup pj.id).isNone).reverse

/-- Place the pending join points in front of a branch: `arms c` renders the branch at the
    position `c` where they are all in scope. -/
def placeJoins (p : Pos) (arms : Core → TermElabM Out) : TermElabM Out := do
  let c := p.core
  let pends := p.pending
  let rec go (c : Core) : List Pend → TermElabM Out
    | [] => arms c
    | pj :: rest => do
        let body ← pj.k (.unk (.out c.du c.depth)) { c with du := c.du + 1 }
        let main ← go { c with jd := c.jd + 1, placed := (pj.id, c.jd) :: c.placed } rest
        let ty ← match pj.ty? with | some t => pure t | none => `(_)
        return { stx := ← `(LeanScript.Branch.join (d := $(quote c.depth)) $ty .many .many $(body.stx) $(main.stx)),
                 lv := lmeet body.lv main.lv }
  let br ← go c pends
  return { stx := ← `(LeanScript.Term.branch $(br.stx)), lv := br.lv }

/-- The union branches `Branches.two`/`Branches.cons` of rendered branches. -/
def branchesStx (d : Nat) : List Lean.Term → TermElabM Lean.Term
  | [a, b] => `(LeanScript.Branches.two (d := $(quote d)) [] [] $a $b)
  | a :: rest => do `(LeanScript.Branches.cons (d := $(quote d)) [] $a $(← branchesStx d rest))
  | [] => throwError "a union has at least two constructors"

/-- A case analysis of a union (or a record) of `n` fields: the error when the scrutinee is not
    neutral. -/
def needNeutral (s : Sem) (what : String) : TermElabM Unit := do
  unless s.isNeutral do
    throwError "cannot take apart a value of unknown shape (a Lean term) while normalising: {what}"

end LeanScript.Anf

end
