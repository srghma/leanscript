module

public meta import LeanScript.Gen.Translate

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Printing the intermediate form

The last stage of the generators: `CIR` and `FIR` are printed as syntax of
`LeanScript.Ty`, `Fld`, `Decl`, … and of the term formers.  Every identifier is
written in a quotation inside `LeanScript`, so it is resolved here and the syntax can
be elaborated in any scope.

Blocks are numbered oldest first (`b`); a name seen from `c` visible blocks is `Ref.here`
under `c - 1 - b` `Ref.there`s.
-/

open Lean Meta Elab

namespace LeanScript.Gen

/-- A reference to member `j` of absolute block `b`, seen from `c` visible blocks. -/
def refStx (c b j : Nat) : MetaM Lean.Term := do
  let mut r ← `(Ref.here $(quote j))
  for _ in [0:c - 1 - b] do
    r ← `(Ref.there $r)
  return r

/-- A block, seen from `c` visible blocks. -/
def brefStx (c b : Nat) : MetaM Lean.Term := do
  let mut r ← `(BRef.here)
  for _ in [0:c - 1 - b] do
    r ← `(BRef.there $r)
  return r

/-- An integer literal. -/
def intStx (i : Int) : MetaM Lean.Term :=
  if i < 0 then `(- $(quote i.natAbs)) else pure (quote i.toNat)

/-- A closed type, seen from `c` visible blocks; type variable `i` is `vars[i]`. -/
partial def CIR.stx (c : Nat) (vars : Array Ident) : CIR → MetaM Lean.Term
  | .prim p => `(Ty.prim $p rfl)
  | .fn a b => do `(Ty.fn $(← a.stx c vars) $(← b.stx c vars))
  | .array a => do `(Ty.array $(← a.stx c vars))
  | .enum n s => do `(Ty.enum ⟨$(quote (n - 3)), $(← intStx s)⟩)
  | .record f fs => do `(Ty.record $(← f.stx c vars) $(← fieldsStx c vars fs.toList))
  | .union cs => do `(Ty.union $(← ctorsStx c vars cs.toList))
  | .data b j => do `(Ty.data $(← refStx c b j))
  | .var i => pure vars[i]!
where
  fieldsStx (c : Nat) (vars : Array Ident) : List CIR → MetaM Lean.Term
    | [] => unreachable!
    | [t] => do `(Fields.one $(← t.stx c vars))
    | t :: ts => do `(Fields.cons $(← t.stx c vars) $(← fieldsStx c vars ts))
  ctorStx (c : Nat) (vars : Array Ident) (fs : Array CIR) : MetaM Lean.Term := do
    if fs.isEmpty then `(Ctor.nullary) else `(Ctor.fields $(← fieldsStx c vars fs.toList))
  ctorsStx (c : Nat) (vars : Array Ident) : List (Array CIR) → MetaM Lean.Term
    | [a, b] => do `(Ctors.two $(← ctorStx c vars a) $(← ctorStx c vars b))
    | a :: rest => do `(Ctors.cons $(← ctorStx c vars a) $(← ctorsStx c vars rest))
    | _ => unreachable!

/-- A field of a body of block `c` (so `c` blocks are visible to it); hole `i` is member
    `pos[i]` of the block. -/
partial def FIR.stx (c : Nat) (pos : Std.HashMap Nat Nat) : FIR → MetaM Lean.Term
  | .hole i => `(Fld.hole $(quote pos[i]!) (by decide))
  | .old t => do `(Fld.old $(← t.stx c #[]))
  | .array f => do `(Fld.array $(← f.stx c pos))
  | .fn a f => do `(Fld.fn $(← a.stx c #[]) $(← f.stx c pos))

def fldsStx (c : Nat) (pos : Std.HashMap Nat Nat) : List FIR → MetaM Lean.Term
  | [] => unreachable!
  | [f] => do `(Flds.one $(← f.stx c pos))
  | f :: fs => do `(Flds.cons $(← f.stx c pos) $(← fldsStx c pos fs))

def bctorStx (c : Nat) (pos : Std.HashMap Nat Nat) (fs : Array FIR) : MetaM Lean.Term := do
  if fs.isEmpty then `(BCtor.nullary) else `(BCtor.fields $(← fldsStx c pos fs.toList))

def bctorsStx (c : Nat) (pos : Std.HashMap Nat Nat) : List (Array FIR) → MetaM Lean.Term
  | [a, b] => do `(BCtors.two $(← bctorStx c pos a) $(← bctorStx c pos b))
  | a :: rest => do `(BCtors.cons $(← bctorStx c pos a) $(← bctorsStx c pos rest))
  | _ => unreachable!

/-- The constructors of a union whose base is constructor `p`. -/
def altsStx (c : Nat) (pos : Std.HashMap Nat Nat) : List (Array FIR) → Nat → MetaM Lean.Term
  | [a, b], 0 => do `(Alts.two₁ $(← bctorStx c pos a) $(← bctorStx c pos b))
  | [a, b], _ => do `(Alts.two₂ $(← bctorStx c pos a) $(← bctorStx c pos b))
  | a :: rest, 0 => do `(Alts.here $(← bctorStx c pos a) $(← bctorsStx c pos rest))
  | a :: rest, p + 1 => do `(Alts.there $(← bctorStx c pos a) $(← altsStx c pos rest p))
  | _, _ => unreachable!

/-- The member declarations of block `b` (seen from itself: `b` older blocks). -/
def Block.memsStx (B : Block) (b : Nat) : MetaM Lean.Term := do
  let pos : Std.HashMap Nat Nat := B.members.zipIdx.foldl (fun m (x, i) => m.insert x i) {}
  let mut mems ← `(Mems.nil)
  for j in (List.range B.members.size).reverse do
    let ctors := B.fields[j]!
    let d ← if ctors.size = 1 then
        let fs := ctors[0]!
        if fs.size = 1 then `(Decl.wrap $(← fs[0]!.stx b pos))
        else `(Decl.record $(← fs[0]!.stx b pos) $(← fldsStx b pos fs[1:].toArray.toList))
      else `(Decl.union $(← altsStx b pos ctors.toList B.bases[j]!))
    mems ← `(Mems.cons $d $mems)
  return mems

/-! ## Terms -/

/-- Constructor `p` of `m` constructors, as a `CtorIx`. -/
def ctorIxStx (m p : Nat) : MetaM Lean.Term := do
  let mut r ← if p + 2 < m then `(CtorIx.head) else if p + 2 = m then `(CtorIx.two₁)
    else `(CtorIx.two₂)
  for _ in [0:min p (m - 2)] do
    r ← `(CtorIx.tail $r)
  return r

/-- A list of terms as `Args`. -/
def argsStx (as : List Lean.Term) : MetaM Lean.Term := do
  let mut r ← `(Args.nil)
  for a in as.reverse do
    r ← `(Args.cons $a $r)
  return r

/-- The value built by constructor `p` of `m` constructors, from the terms of its fields:
    the field itself (one constructor, one field), a record, an enum constructor (`enum`
    gives the number of constructors and the shift), or a union constructor. -/
def ctorBodyStx (m p : Nat) (enum : Option (Nat × Int)) (args : List Lean.Term) :
    MetaM Lean.Term := do
  if m = 1 then
    match args with
    | [a] => return a
    | _ => `(LeanScript.Term.record_mk $(← argsStx args))
  else if let some (n, s) := enum then
    `(LeanScript.Term.enum_mk ⟨$(quote (n - 3)), $(← intStx s)⟩ ⟨$(quote p), by decide⟩)
  else
    `(LeanScript.Term.union_mk $(← ctorIxStx m p) $(← argsStx args))

end LeanScript.Gen

end
