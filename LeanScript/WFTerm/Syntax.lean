module

public import LeanScript.Term.Semantics.Eval

@[expose] public section

set_option autoImplicit false

/-!
# `WFTerm`: well-founded recursion around normal-form terms (proof-carrying calls)

`LeanScript.Term` is a language of **total** normal-form terms: its only recursion is structural
(`nat_rec`, `array_foldl`, `data_rec`, `data_brec`).  `WFTerm` wraps it and adds **well-founded
recursion**, without fuel, without measures and without `Acc` data: every termination argument is
a `Prop` carried by the syntax, and is erased by code generation.

```
Atom    ::= a Term (Term Δ d [] Γ τ [] o)       -- a total, call-free computation
Comp    ::= self args                           -- a recursive call (with its decrease proof)
          | g args                              -- a call of a global function g
          | Atom                                -- share: a total value, computed once
          | map (fun x => WFTerm) Atom          -- (the body knows x ∈ list)
          | foldl (fun acc x => WFTerm) Atom Atom   -- (idem)
WFTerm  ::= ret Atom                            -- tail statements
          | if Atom then WFTerm else WFTerm
          | let v := Comp in WFTerm             -- letE: the one binding construct
          | join j (v) := WFTerm in WFTerm      -- a non-recursive join point
          | joinrec j (v) [R] := WFTerm in WFTerm   -- a recursive join point (a loop)
          | jump j Atom
Program ::= global functions (each: fix self xs. WFTerm) ; main WFTerm
```

**Wrapping `Term`.**  The call-free layer is `Term` itself: an `Atom Δ Γ τ` is a normal-form
statement `Term Δ d [] (WCtx.toU Γ) τ [] o` whose unknowns are the variables of the `WFTerm`
layer (every such variable is a runtime value, so it is an *unknown* for the normaliser of
`Term`).  An atom is evaluated by `Term.eval`, which is total and structural, so the path
conditions and decrease proofs below may mention `WFAtom.eval`, which is defined before
`WFTerm`: no induction–recursion is needed.

**Well-founded recursion.**  As in the grammar `PCL`:

* a **global function** (`WFFn`, `WFGlobals`) has a precondition and a postcondition, and a
  well-founded relation `R` on its argument tuples.  Inside its body, it calls itself by
  `WFComp.self`, which carries the proof `dec` that the arguments are `R`-smaller than the
  current parameters *whenever the call is reached* (under the path condition `G`).  A call of a
  global function defined before (`WFComp.call`) only proves the precondition;
* a **join point** (`join`/`jump`) names the continuation of a branch;
* a **recursive join point** (`joinrec`) is a loop: inside its body, the precondition of the
  back edge is `P e v ∧ R e v x`, so every back jump carries its own decrease proof.

The **path condition** `G : WEnv Δ Γ → Prop` is strengthened by each `ite` branch, by the
precondition of the enclosing function, by the membership `x ∈ l` in the body of a `map`/`foldl`,
and by the fact each computation establishes (`WFComp`'s last index `F`: the postcondition of the
callee, the equation of a shared value, nothing for a fold).  Every statement carries its
postcondition `Q`, which each `ret` proves.

The evaluator (`LeanScript.WFTerm.Eval`) is total and structural on the syntax; the global
functions and the recursive join points are run by `WellFounded.fix`, whose well-foundedness
proofs are `Prop`s: nothing is checked, counted or measured at runtime.

The environments of this layer are right-nested pairs (`WEnv`), so that the projections of an
environment extended by one value compute by `rfl` (a `Tuple` would need `Tuple.tail_cons`).
-/

namespace LeanScript

variable {ks : List Nat}

/-! ## Contexts and environments of the `WFTerm` layer -/

/-- The variables of the `WFTerm` layer: their types, innermost first. -/
abbrev WCtx (ks : List Nat) : Type := List (Ty ks)

/-- The variables of the `WFTerm` layer, as unknowns of `Term` (used `many` times, level `0`). -/
def WCtx.toU : WCtx ks → UCtx ks
  | [] => []
  | τ :: Γ => ⟨τ, .many, 0⟩ :: WCtx.toU Γ

/-- Values of the variables of the `WFTerm` layer: right-nested pairs. -/
@[reducible] def WEnv (Δ : DSig ks) : WCtx ks → Type
  | [] => Unit
  | τ :: Γ => Ty.Den Δ τ × WEnv Δ Γ

/-- The same values, as an environment of unknowns of `Term`. -/
def WEnv.toU {Δ : DSig ks} : {Γ : WCtx ks} → WEnv Δ Γ → UEnv Δ (WCtx.toU Γ)
  | [], _ => PUnit.unit
  | _ :: _, e => Tuple.cons e.1 (WEnv.toU e.2)

/-! ## Atoms: the call-free layer is `Term` -/

/-- **An atom**: a total, call-free computation of type `τ`, written in the normal-form language
`Term`, whose unknowns are the variables `Γ` of the `WFTerm` layer. -/
structure WFAtom (Δ : DSig ks) (Γ : WCtx ks) (τ : Ty ks) where
  /-- The depth of the term (irrelevant for its value). -/
  {d : Nat}
  /-- The level of the term (irrelevant for its value). -/
  {o : Lvl}
  /-- The term. -/
  term : Term Δ d [] (WCtx.toU Γ) τ [] o

/-- The value of an atom. -/
def WFAtom.eval {Δ : DSig ks} {Γ : WCtx ks} {τ : Ty ks} (a : WFAtom Δ Γ τ) (e : WEnv Δ Γ) :
    Ty.Den Δ τ :=
  a.term.eval PUnit.unit e.toU PUnit.unit

/-- A pure expression of `Term`, as an atom (`ret p`). -/
abbrev WFAtom.pure {Δ : DSig ks} {Γ : WCtx ks} {τ : Ty ks} {o : Lvl}
    (p : PExpr Δ [] (WCtx.toU Γ) τ o) : WFAtom Δ Γ τ :=
  ⟨(Term.ret p : Term Δ 0 [] (WCtx.toU Γ) τ [] o)⟩

/-- The value of an atom of list type, as a Lean list. -/
abbrev WFAtom.evalList {Δ : DSig ks} {Γ : WCtx ks} {τ : Ty ks} (a : WFAtom Δ Γ (.list τ))
    (e : WEnv Δ Γ) : List (Ty.Den Δ τ) :=
  a.eval e

/-- The value of an atom of type `bool`, as a Lean `Bool`. -/
abbrev WFAtom.evalBool {Δ : DSig ks} {Γ : WCtx ks} (a : WFAtom Δ Γ .bool) (e : WEnv Δ Γ) :
    Bool :=
  a.eval e

/-- A tuple of atoms, one for each entry of `ts` (the arguments of a call). -/
inductive WFAtoms (Δ : DSig ks) (Γ : WCtx ks) : WCtx ks → Type where
  | nil : WFAtoms Δ Γ []
  | cons {τ : Ty ks} {ts : WCtx ks} : WFAtom Δ Γ τ → WFAtoms Δ Γ ts → WFAtoms Δ Γ (τ :: ts)

/-- The values of a tuple of atoms. -/
def WFAtoms.eval {Δ : DSig ks} {Γ : WCtx ks} : {ts : WCtx ks} → WFAtoms Δ Γ ts → WEnv Δ Γ →
    WEnv Δ ts
  | [], .nil, _ => ()
  | _ :: _, .cons a as, e => (a.eval e, as.eval e)

/-! ## Global functions -/

/-- The signature of a global (well-founded recursive) function: parameters, result type,
precondition and postcondition. -/
structure WFFn (Δ : DSig ks) where
  params : WCtx ks
  ret : Ty ks
  pre : WEnv Δ params → Prop
  post : WEnv Δ params → Ty.Den Δ ret → Prop

/-- The meaning of a function: defined on the arguments satisfying its precondition, with
results satisfying its postcondition. -/
abbrev WFFnVal {Δ : DSig ks} (f : WFFn Δ) : Type :=
  (x : WEnv Δ f.params) → f.pre x → {v : Ty.Den Δ f.ret // f.post x v}

/-- Typed de Bruijn indices of global functions. -/
inductive WFFnVar {Δ : DSig ks} : List (WFFn Δ) → WFFn Δ → Type where
  | here {fs : List (WFFn Δ)} {f : WFFn Δ} : WFFnVar (f :: fs) f
  | there {fs : List (WFFn Δ)} {f g : WFFn Δ} : WFFnVar fs f → WFFnVar (g :: fs) f

/-- Values of the global functions. -/
@[reducible] def WFFEnv {Δ : DSig ks} : List (WFFn Δ) → Type
  | [] => Unit
  | f :: fs => WFFnVal f × WFFEnv fs

/-- Lookup of a global function. -/
def WFFnVar.get {Δ : DSig ks} : {fs : List (WFFn Δ)} → {f : WFFn Δ} → WFFnVar fs f →
    WFFEnv fs → WFFnVal f
  | _ :: _, _, .here, fe => fe.1
  | _ :: _, _, .there i, fe => i.get fe.2

/-! ## Join points -/

/-- The join points in scope in context `Γ`, for statements of result type `t`.  `bind js s P Q`
adds a join point defined in the current context, whose parameter (of type `s`) satisfies `P`,
and which establishes `Q`; `wk js s` is the scope `js` seen under one more variable of type `s`.
A recursive join point is an ordinary `bind` entry inside its own body, whose precondition
includes the decrease of the back edge (see `WFTerm.joinrec`). -/
inductive WFJScope (Δ : DSig ks) : WCtx ks → Ty ks → Type where
  | nil {Γ : WCtx ks} {t : Ty ks} : WFJScope Δ Γ t
  | bind {Γ : WCtx ks} {t : Ty ks} (js : WFJScope Δ Γ t) (s : Ty ks)
      (P : WEnv Δ Γ → Ty.Den Δ s → Prop) (Q : WEnv Δ Γ → Ty.Den Δ t → Prop) : WFJScope Δ Γ t
  | wk {Γ : WCtx ks} {t : Ty ks} (js : WFJScope Δ Γ t) (s : Ty ks) : WFJScope Δ (s :: Γ) t

/-- Typed de Bruijn indices of join points. -/
inductive WFJVar {Δ : DSig ks} : {Γ : WCtx ks} → {t : Ty ks} → WFJScope Δ Γ t → Type where
  | here {Γ : WCtx ks} {t : Ty ks} {js : WFJScope Δ Γ t} {s : Ty ks}
      {P : WEnv Δ Γ → Ty.Den Δ s → Prop} {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} :
      WFJVar (.bind js s P Q)
  | there {Γ : WCtx ks} {t : Ty ks} {js : WFJScope Δ Γ t} {s : Ty ks}
      {P : WEnv Δ Γ → Ty.Den Δ s → Prop} {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} :
      WFJVar js → WFJVar (.bind js s P Q)
  | wk {Γ : WCtx ks} {t : Ty ks} {js : WFJScope Δ Γ t} {s : Ty ks} : WFJVar js → WFJVar (.wk js s)

/-- The parameter type of a join point. -/
def WFJVar.arg {Δ : DSig ks} : {Γ : WCtx ks} → {t : Ty ks} → {js : WFJScope Δ Γ t} → WFJVar js →
    Ty ks
  | _, _, .bind _ s _ _, .here => s
  | _, _, .bind _ _ _ _, .there i => i.arg
  | _, _, .wk _ _, .wk i => i.arg

/-- The precondition of a join point, read at the current environment. -/
def WFJVar.pre {Δ : DSig ks} : {Γ : WCtx ks} → {t : Ty ks} → {js : WFJScope Δ Γ t} →
    (i : WFJVar js) → WEnv Δ Γ → Ty.Den Δ i.arg → Prop
  | _, _, .bind _ _ P _, .here, e => P e
  | _, _, .bind _ _ _ _, .there i, e => i.pre e
  | _, _, .wk _ _, .wk i, e => i.pre e.2

/-- The postcondition established by a join point, read at the current environment. -/
def WFJVar.post {Δ : DSig ks} : {Γ : WCtx ks} → {t : Ty ks} → {js : WFJScope Δ Γ t} →
    (i : WFJVar js) → WEnv Δ Γ → Ty.Den Δ t → Prop
  | _, _, .bind _ _ _ Q, .here, e => Q e
  | _, _, .bind _ _ _ _, .there i, e => i.post e
  | _, _, .wk _ _, .wk i, e => i.post e.2

/-! ## The enclosing recursive function -/

/-- The innermost enclosing recursive function: its parameters, result type, well-founded
relation, precondition, postcondition, and how to read its current parameters from the
environment. -/
structure WFSelf (Δ : DSig ks) (Γ : WCtx ks) where
  params : WCtx ks
  ret : Ty ks
  R : WEnv Δ params → WEnv Δ params → Prop
  pre : WEnv Δ params → Prop
  post : WEnv Δ params → Ty.Den Δ ret → Prop
  cur : WEnv Δ Γ → WEnv Δ params

/-- The same function, seen under one more variable. -/
abbrev WFSelf.push {Δ : DSig ks} {Γ : WCtx ks} (sf : WFSelf Δ Γ) (t : Ty ks) :
    WFSelf Δ (t :: Γ) :=
  { sf with cur := fun e => sf.cur e.2 }

/-- The function whose body is being defined: its parameters are the whole context. -/
abbrev WFSelf.top {Δ : DSig ks} (f : WFFn Δ) (R : WEnv Δ f.params → WEnv Δ f.params → Prop) :
    WFSelf Δ f.params :=
  { params := f.params, ret := f.ret, R := R, pre := f.pre, post := f.post, cur := id }

/-! ## Computations and statements -/

mutual

/-- **Computations**: the steps whose value a `let` binds.  In context `Γ`, under the path
condition `G`, inside the recursive function `sf` (if any), a computation produces a value of type
`u` and establishes the fact `F` about it (in the context extended by that value).  The
continuation of the `let` runs under `G ∧ F` (`WFTerm.letE`). -/
inductive WFComp {ks : List Nat} (Δ : DSig ks) (GL : List (WFFn Δ)) :
    (Γ : WCtx ks) → (WEnv Δ Γ → Prop) → Option (WFSelf Δ Γ) →
    (u : Ty ks) → (WEnv Δ (u :: Γ) → Prop) → Type where
  /-- `self args`: a recursive call of the enclosing function, with the proofs that the call goes
  down (`dec`) and that the arguments satisfy the precondition (`hpre`) whenever it is reached;
  afterwards the result satisfies the postcondition. -/
  | self {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : WFSelf Δ Γ}
      (args : WFAtoms Δ Γ sf.params)
      (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
      (hpre : ∀ e, G e → sf.pre (args.eval e)) :
      WFComp Δ GL Γ G (some sf) sf.ret (fun e => sf.post (args.eval e.2) e.1)
  /-- `g args`: a call of the global function `g`, with the proof that the arguments satisfy its
  precondition; afterwards the result satisfies its postcondition.  (No decrease proof: the
  callee is complete.) -/
  | call {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {f : WFFn Δ}
      (i : WFFnVar GL f) (args : WFAtoms Δ Γ f.params)
      (hpre : ∀ e, G e → f.pre (args.eval e)) :
      WFComp Δ GL Γ G sf f.ret (fun e => f.post (args.eval e.2) e.1)
  /-- A **shared** total value (an atom): computed once, afterwards the new variable is known to
  equal it. -/
  | share {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {s : Ty ks}
      (a : WFAtom Δ Γ s) :
      WFComp Δ GL Γ G sf s (fun e => e.1 = a.eval e.2)
  /-- `List.map (fun x => body) l`.  The body may make calls (recursive calls of the enclosing
  function included), and runs under the fact `x ∈ l`, which its decrease proofs may use (the
  program holds no proof term for it).  It has no join point in scope and no postcondition. -/
  | map {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {s u : Ty ks}
      (l : WFAtom Δ Γ (.list s))
      (body : WFTerm Δ GL (s :: Γ)
        (fun e => G e.2 ∧ e.1 ∈ l.evalList e.2)
        (sf.map (·.push s)) u (fun _ _ => True) .nil) :
      WFComp Δ GL Γ G sf (.list u) (fun _ => True)
  /-- `List.foldl (fun acc x => body) init l`: the body binds the element `x` and the
  accumulator `acc` (index `0`), and runs under the fact `x ∈ l`. -/
  | foldl {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {s u : Ty ks}
      (l : WFAtom Δ Γ (.list s)) (init : WFAtom Δ Γ u)
      (body : WFTerm Δ GL (u :: s :: Γ)
        (fun e => G e.2.2 ∧ e.2.1 ∈ l.evalList e.2.2)
        ((sf.map (·.push s)).map (·.push u)) u (fun _ _ => True) .nil) :
      WFComp Δ GL Γ G sf u (fun _ => True)

/-- **Statements** of result type `t` in context `Γ`, reached under the path condition `G`,
with the global functions `GL` in scope, inside the recursive function `sf` (if any),
establishing the postcondition `Q`, with the join points `js` in scope. -/
inductive WFTerm {ks : List Nat} (Δ : DSig ks) (GL : List (WFFn Δ)) :
    (Γ : WCtx ks) → (WEnv Δ Γ → Prop) → Option (WFSelf Δ Γ) →
    (t : Ty ks) → (WEnv Δ Γ → Ty.Den Δ t → Prop) → WFJScope Δ Γ t → Type where
  /-- Return a total value, which satisfies the postcondition. -/
  | ret {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
      {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}
      (a : WFAtom Δ Γ t) (post : ∀ e, G e → Q e (a.eval e)) :
      WFTerm Δ GL Γ G sf t Q js
  /-- `if c then a else b`, in tail position; each branch knows the outcome of the test. -/
  | ite {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
      {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}
      (c : WFAtom Δ Γ .bool)
      (a : WFTerm Δ GL Γ (fun e => G e ∧ c.evalBool e = true) sf t Q js)
      (b : WFTerm Δ GL Γ (fun e => G e ∧ c.evalBool e = false) sf t Q js) :
      WFTerm Δ GL Γ G sf t Q js
  /-- `let v := c in k`: the value of the computation `c` is bound to a new variable (index `0`
  of `k`), and `k` runs under the path condition and the fact `F` that `c` establishes. -/
  | letE {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
      {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t} {u : Ty ks}
      {F : WEnv Δ (u :: Γ) → Prop}
      (c : WFComp Δ GL Γ G sf u F)
      (k : WFTerm Δ GL (u :: Γ) (fun e => G e.2 ∧ F e) (sf.map (·.push u)) t
        (fun e v => Q e.2 v) (.wk js u)) :
      WFTerm Δ GL Γ G sf t Q js
  /-- `join j (v : s) := body in m`, in tail position: the join point `j` (whose parameter
  satisfies `P`) is in scope in `m`. -/
  | join {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
      {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}
      (s : Ty ks) (P : WEnv Δ Γ → Ty.Den Δ s → Prop)
      (body : WFTerm Δ GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
        (fun e r => Q e.2 r) (.wk js s))
      (m : WFTerm Δ GL Γ G sf t Q (.bind js s P Q)) : WFTerm Δ GL Γ G sf t Q js
  /-- `joinrec j (x : s) [R, wf] := body in m`, in tail position: a **recursive join point** (a
  loop).  Inside the body, the precondition of `j` is `P e v ∧ R e v x`: each back edge proves
  that the new parameter `v` is below the current one `x` along `R e` (well-founded by `wf`).
  From `m`, `j` only needs `P`. -/
  | joinrec {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
      {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}
      (s : Ty ks) (P : WEnv Δ Γ → Ty.Den Δ s → Prop)
      (R : WEnv Δ Γ → Ty.Den Δ s → Ty.Den Δ s → Prop)
      (wf : ∀ e, WellFounded (R e))
      (body : WFTerm Δ GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
        (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
          (fun e r => Q e.2 r)))
      (m : WFTerm Δ GL Γ G sf t Q (.bind js s P Q)) : WFTerm Δ GL Γ G sf t Q js
  /-- `jump j a`, in tail position: run the join point `j` on `a`, with the proof that `a`
  satisfies its precondition (for a back edge of a recursive join point, this includes the
  decrease); its result satisfies the current postcondition. -/
  | jump {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
      {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}
      (i : WFJVar js) (a : WFAtom Δ Γ i.arg)
      (hpre : ∀ e, G e → i.pre e (a.eval e))
      (hpost : ∀ e, G e → ∀ r, i.post e r → Q e r) : WFTerm Δ GL Γ G sf t Q js

end

/-! ## Global functions and programs -/

/-- **The global functions** of a program, each defined by well-founded recursion: a body in
which `WFComp.self` calls the function itself along the well-founded relation `R`, and
`WFComp.call` calls the functions defined before it. -/
inductive WFGlobals (Δ : DSig ks) : List (WFFn Δ) → Type where
  | nil : WFGlobals Δ []
  | cons {GL : List (WFFn Δ)} (gs : WFGlobals Δ GL) (f : WFFn Δ)
      (R : WEnv Δ f.params → WEnv Δ f.params → Prop) (wf : WellFounded R)
      (body : WFTerm Δ GL f.params f.pre (some (WFSelf.top f R)) f.ret f.post .nil) :
      WFGlobals Δ (f :: GL)

/-- **A program**: global functions and a main statement (with no variable), whose answer
satisfies `Q`. -/
structure WFProgram (Δ : DSig ks) (τ : Ty ks) (Q : Ty.Den Δ τ → Prop) where
  GL : List (WFFn Δ)
  globals : WFGlobals Δ GL
  main : WFTerm Δ GL [] (fun _ => True) none τ (fun _ r => Q r) .nil

/-! ## Derived forms: `let` of each kind of computation -/

section Derived
variable {Δ : DSig ks} {GL : List (WFFn Δ)} {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {t : Ty ks}
  {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}

/-- `let v := self args in k` (`letE` of `WFComp.self`). -/
@[reducible] def WFTerm.fixSelfCall {sf : WFSelf Δ Γ}
    (args : WFAtoms Δ Γ sf.params)
    (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
    (hpre : ∀ e, G e → sf.pre (args.eval e))
    (k : WFTerm Δ GL (sf.ret :: Γ) (fun e => G e.2 ∧ sf.post (args.eval e.2) e.1)
      (some (sf.push sf.ret)) t (fun e v => Q e.2 v) (.wk js sf.ret)) :
    WFTerm Δ GL Γ G (some sf) t Q js :=
  .letE (.self args dec hpre) k

/-- `let v := g args in k`, for a global function `g` (`letE` of `WFComp.call`). -/
@[reducible] def WFTerm.gCall {sf : Option (WFSelf Δ Γ)} {f : WFFn Δ}
    (i : WFFnVar GL f) (args : WFAtoms Δ Γ f.params)
    (hpre : ∀ e, G e → f.pre (args.eval e))
    (k : WFTerm Δ GL (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1)
      (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret)) :
    WFTerm Δ GL Γ G sf t Q js :=
  .letE (.call i args hpre) k

/-- `let v := a in k`, a pure `let` (`letE` of `WFComp.share`). -/
@[reducible] def WFTerm.plet {sf : Option (WFSelf Δ Γ)} {s : Ty ks} (a : WFAtom Δ Γ s)
    (k : WFTerm Δ GL (s :: Γ) (fun e => G e.2 ∧ e.1 = a.eval e.2) (sf.map (·.push s)) t
      (fun e v => Q e.2 v) (.wk js s)) :
    WFTerm Δ GL Γ G sf t Q js :=
  .letE (.share a) k

end Derived

end LeanScript

end
