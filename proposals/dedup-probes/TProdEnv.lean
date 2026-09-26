import Mathlib.Data.Prod.TProd

/-! Probe for proposals/DeduplicationProposal.md, section 2.
Needs Mathlib v4.34.0.  Expected: compiles with no errors.
`GlobalEnv`-style environment as `List.TProd`, with the existing `get`/`append`
written by structural matching and a concrete lookup checked by `rfl`. -/

inductive DBP {α β : Type} (f : α → β) : List α → β → Type
  | head : ∀ {x : α} {xs : List α}, DBP f (x :: xs) (f x)
  | tail : ∀ {x : α} {xs : List α} {b : β}, DBP f xs b → DBP f (x :: xs) b

variable {ι : Type} (D : ι → Type)

abbrev Env (Γ : List ι) : Type := List.TProd D Γ

def Env.get : {Γ : List ι} → {τ : ι} → DBP id Γ τ → Env D Γ → D τ
  | _ :: _, _, .head, env => env.1
  | _ :: _, _, .tail v, env => Env.get v env.2

def Env.append : {as : List ι} → {Γ : List ι} → Env D as → Env D Γ → Env D (as ++ Γ)
  | [], _, _, env => env
  | _ :: _, _, vs, env => (vs.1, Env.append vs.2 env)

example (a b : ι) (x : D a) (y : D b) : Env.get D (.tail .head) ((x, y, PUnit.unit) : Env D [a, b]) = y := rfl
