module

public import TermTests.ToTermTest.Basic
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `#leanscript_to_term`, run: the cache and user-defined datatypes
-/

namespace TermTests.ToTerm

open LeanScript

/-- Running a closed term of `sig0`; see `TermTests.ToTermTest.Basic`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-! ## The cache

`twiceA` and `twiceB` are different definitions of the same shape, so the second one is
not stored twice: it is merged into the tree of the first. -/

#leanscript_to_term_cache_clear

@[inline] def twiceA (n : Nat) : Nat := n + n

@[inline] def twiceB (m : Nat) : Nat := m + m

def usesA : Nat := twiceA 2

def usesB : Nat := twiceB 2

def usesAagain : Nat := twiceA 5

def usesA_term := (#leanscript_to_term usesA : Term sigAdd [] _ (TyWf.prim .nat) .comp)

/-- `twiceB` has the shape of `twiceA`, which is translated already. -/
def usesB_term := (#leanscript_to_term usesB : Term sigAdd [] _ (TyWf.prim .nat) .comp)

/-- `twiceA` is translated already: this is a plain cache hit. -/
def usesAagain_term := (#leanscript_to_term usesAagain : Term sigAdd [] _ (TyWf.prim .nat) .comp)

example : runAdd usesA_term = 4 := rfl
example : runAdd usesB_term = 4 := rfl
example : runAdd usesAagain_term = 10 := rfl

-- Five definitions were translated (`usesA`, `twiceA`, `usesB`, `twiceB`, `usesAagain`;
-- `Nat.add` is a signature global, not a translation), `twiceB` turned out to have the
-- shape of `twiceA` and was merged into its tree, and the two later uses were found in
-- the cache.
/-- info: entries: 5, hits: 2, shape merges: 1 -/
#guard_msgs (info) in
#leanscript_to_term_cache_stats

/-! ## A user-defined tagged union, a pair and a thunk -/

inductive Shape where
  | circle (radius : Nat)
  | rect (width height : Nat)
  deriving LeanScriptTyWf

def widthOf (s : Shape) : Nat :=
  match s with
  | .circle r => r
  | .rect w _ => w

def widthOf_term :=
  (#leanscript_to_term widthOf :
    Term sig0 [] _ (tyWfOf Shape ⇒ TyWf.prim .nat) .lam)

def aRect : Shape := .rect 3 4

def aRect_term := (#leanscript_to_term aRect : Term sig0 [] _ (tyWfOf Shape) .val)

example : run widthOf_term (run aRect_term) = 3 := rfl

def swap (p : Nat × Bool) : Bool × Nat := (p.2, p.1)

def swap_term :=
  (#leanscript_to_term swap :
    Term sig0 [] _ (tyWfOf (Nat × Bool) ⇒ tyWfOf (Bool × Nat)) .lam)

def aPair : Nat × Bool := (7, true)

def aPair_term := (#leanscript_to_term aPair : Term sig0 [] _ (tyWfOf (Nat × Bool)) .val)

example : (run swap_term (run aPair_term)).1 = true := rfl
example : (run swap_term (run aPair_term)).2.1 = (7 : Nat) := rfl

@[inline] def delayed : Thunk Nat := Thunk.mk (fun _ => 6)

def delayed_term :=
  (#leanscript_to_term delayed :
    Term sig0 [] _ (TyWf.thunk (TyWf.prim .nat)) .val)

def forced : Nat := delayed.get

def forced_term := (#leanscript_to_term forced : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : run forced_term = 6 := rfl

/-! ## The type of the translation, inferred

With `(sig := …)` the signature does not have to be read off the expected type, so the
translation can be written with no type ascription at all. -/

def inferred_term := #leanscript_to_term (sig := sigAdd) sumUpTo

example : runAdd inferred_term 4 = 6 := rfl


end TermTests.ToTerm

end
