module

public import LeanScript.TermElab.Anf.Src

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Semantic values of the normaliser

Semantic values `Sem`, positions in the output, join points and continuations.
-/

open Lean Meta Elab Term

namespace LeanScript.Anf

/-! ## Semantic values -/

/-- A known value bound by `letV`: its position in the known context, and its level. -/
structure KRef where
  pos : Nat
  lv : Lvl
  deriving Inhabited, Repr, BEq

/-- An unknown: at position `pos` of the output's context of unknowns, bound at level `lv`; or
    variable `i` of the enclosing context. -/
inductive URef where
  | out (pos lv : Nat)
  | free (i : Nat)
  deriving Inhabited, Repr, BEq

/-- Semantic values. -/
inductive Sem where
  | unk (r : URef)
  | dataOut (b j : Lean.Term) (e : Sem)
  | cond (c a b : Sem)
  | extern (e : Lean.Term) (args : Array Sem)
  | lit (stx : Lean.Term) (val : LitVal)
  | enum (i : Option Nat) (stx : Lean.Term)
  | record (fs : Array Sem) (name : Option KRef)
  | union (pos : Option Nat) (ix : Lean.Term) (fs : Array Sem) (name : Option KRef)
  | array (es : Array Sem) (name : Option KRef)
  | list (es : Array Sem) (name : Option KRef)
  | dataIn (b j : Lean.Term) (e : Sem) (name : Option KRef)
  | ctor (f : Lean.Term) (fs : Array Sem) (shape : Option CtorShape)
  | embed (stx : Lean.Term)
  | clo (env : List Sem) (ty? : Option Lean.Term) (body : Src) (k : KRef)
  | delay (lazy : Bool) (τ? : Option Lean.Term) (env : List Sem) (body : Src) (k : KRef)
  | ascribe (s : Sem) (ty : Lean.Term)
  deriving Inhabited

/-- The smaller of two levels (`none` is the unit). -/
def lmeet : Lvl → Lvl → Lvl
  | none, o => o
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

/-- The value without its type ascriptions. -/
partial def Sem.strip : Sem → Sem
  | .ascribe s _ => s.strip
  | s => s

/-- The name of a value bound by `letV`. -/
def Sem.name? : Sem → Option KRef
  | .record _ n | .union _ _ _ n | .array _ n | .list _ n | .dataIn _ _ _ n => n
  | .clo _ _ _ k | .delay _ _ _ _ k => some k
  | _ => none

mutual
/-- The level of a semantic value: the smallest level of the unknowns it mentions. -/
partial def Sem.lv (s : Sem) : Lvl :=
  match s with
  | .unk (.out _ l) => some l
  | .unk (.free _) => some 0
  | .dataOut _ _ e => e.lv
  | .cond c a b => lmeet c.lv (lmeet a.lv b.lv)
  | .extern _ as => Sem.lvAll as.toList
  | .lit .. | .enum .. | .embed _ => none
  | .ctor _ fs _ => Sem.lvAll fs.toList
  | .ascribe s _ => s.lv
  | s => match s.name? with
    | some k => k.lv
    | none => match s with
      | .record fs _ | .union _ _ fs _ | .array fs _ | .list fs _ => Sem.lvAll fs.toList
      | .dataIn _ _ e _ => e.lv
      | _ => none
/-- The level of several values together. -/
partial def Sem.lvAll : List Sem → Lvl
  | [] => none
  | s :: ss => lmeet s.lv (Sem.lvAll ss)
end

/-- Is a value neutral: an unknown, or an elimination stuck on one? -/
partial def Sem.isNeutral : Sem → Bool
  | .unk _ | .dataOut .. | .cond .. | .extern .. => true
  | .ascribe s _ => s.isNeutral
  | _ => false

/-- Is a value used in place when bound by a source `let` (never shared)? -/
def Sem.trivial (s : Sem) : Bool :=
  match s.strip with
  | .unk _ | .lit .. | .enum .. | .embed _ | .ctor .. => true
  | s => s.name?.isSome

/-! ## Positions, join points, results -/

/-- Where the output is: the numbers of unknowns, known values and join points in scope, the
    depth (the number of bodies around), and the join points placed so far (by identifier,
    with their positions). -/
structure Core where
  du : Nat := 0
  dk : Nat := 0
  jd : Nat := 0
  depth : Nat := 0
  placed : List (Name × Nat) := []
  deriving Inhabited

/-- A statement produced by the normaliser, and its level. -/
structure Out where
  stx : Lean.Term
  lv : Lvl
  deriving Inhabited

/-- A pending join point: the continuation it stands for, placed in front of the next branch or
    inlined where it is jumped to. -/
structure Pend where
  id : Name
  ty? : Option Lean.Term
  k : Sem → Core → TermElabM Out

/-- A position, with the join points still pending (innermost first). -/
structure Pos where
  core : Core := {}
  pend : List Pend := []

/-- The source variables and join points in scope, innermost first. -/
structure Scope where
  vars : List Sem := []
  joins : List Name := []
  deriving Inhabited

/-- The value of source variable `i`: an unknown of the enclosing context past the end. -/
def Scope.var (sc : Scope) (i : Nat) : Sem :=
  if h : i < sc.vars.length then sc.vars[i] else .unk (.free (i - sc.vars.length))

/-- Bind source variables to the values `ss`, the first one innermost (index `0`). -/
def Scope.pushAll (sc : Scope) (ss : List Sem) : Scope := { sc with vars := ss ++ sc.vars }

/-- Bind one more source variable. -/
def Scope.push (sc : Scope) (s : Sem) : Scope := sc.pushAll [s]

/-- The unknowns at positions `du`, …, `du + n - 1`, at level `lv`, the last one innermost:
    the binders of a pattern or a body. -/
def unknowns (n du lv : Nat) : List Sem :=
  (List.range n).reverse.map fun i => .unk (.out (du + i) lv)

/-- What is done with the value of a statement: return it, jump with it to a join point, or
    continue with it. -/
inductive Kont where
  | ret
  | jump (id : Name)
  | fn (k : Sem → Pos → TermElabM Out)

end LeanScript.Anf

end
