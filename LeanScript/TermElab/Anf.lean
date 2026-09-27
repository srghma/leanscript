module

public import LeanScript.Term.TermSubst
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

@[expose] public section

meta section

set_option autoImplicit false

/-!
# A-normalisation: from direct-style source trees to the syntax of A-normal `Term`s

`LeanScript.Term` is strictly A-normal and B-normal (`LeanScript.Term`), but it is convenient
to *write* a term in direct style: `f (if c then g x else 0) + 1`.  Both the notation
`[Term| …]` (`LeanScript.TermElab.Notation`) and the translator `#leanscript_to_term`
(`LeanScript.TermElab.ToTerm`) first build a direct-style source tree `Src`, whose variables are
de Bruijn indices of the source, and then normalise it here into the syntax of a `Term`.

The normaliser is the usual one, in continuation-passing style:

* every operand is normalised to an `Atom`, a pure expression (`PExpr`);
* a value that is taken apart (the argument of `data_out`, the condition of `cond` and `ite`,
  a scrutinee) must be a *neutral* expression (`Neu`): when it is an introduction form the
  normaliser reduces the ι-redex (`data_out` of `data_in`, a case analysis of a literal or a
  constructor: the branch, with the fields bound as by a `let`); when it is of unknown shape (a
  Lean term, the result of a constructor function) it is shared by a `let` first, whose
  variable is neutral;
* every computation (an application, a closure, an extern, a fold, a delay) is named by a
  `Term.letE`, in evaluation order;
* a trivial pure expression (a variable, a literal, `PExpr.isTrivial`) bound by a source
  `let` is used in place; any other pure expression is `Comp.share`d;
* a branch (`if`, `match`) in tail position gets the continuation in each branch; a branch
  anywhere else is the pure conditional `PExpr.cond c a b` when it is an `if` whose branches
  are pure expressions (proposal 4d: `(if c then x + 1 else 0) * 2`, with `+` a cheap extern),
  and otherwise gets a **join point** for the rest of the computation
  (`join j x := rest; …; jump j a`), so the continuation is never duplicated;
* the bodies of closures, folds and delays are normalised on their own, with no join point in
  scope.

Variables are resolved to indices only at the end: an atom names a variable by its *level*
(the number of binders of the output outside it), so it stays valid under the binders the
normaliser adds.  A variable of the enclosing context (free in the source) is shifted past
them, and so is a Lean term embedded in the source (`PExpr.shift`), unless it is generic in
its context (`sumT : {Γ : Ctx ks} → Comp Δ Γ τ`): then it is used as it is.
-/

open Lean Meta Elab

namespace LeanScript.Anf

/-- A de Bruijn index. -/
def dbStx : Nat → MetaM Lean.Term
  | 0 => `(DeBruijn.head)
  | n + 1 => do `(DeBruijn.tail $(← dbStx n))

/-- The variable of de Bruijn index `i`, as a pure expression. -/
def pvarStx (i : Nat) : MetaM Lean.Term := do `(LeanScript.PExpr.var $(← dbStx i))

/-- The variable of de Bruijn index `i`, as a neutral expression. -/
def nvarStx (i : Nat) : MetaM Lean.Term := do `(LeanScript.Neu.var $(← dbStx i))

/-- What an introduction form is made of, for the ι-reductions the normaliser performs. -/
inductive Intro where
  /-- An introduction form of unknown shape (or of no interest): never reduced. -/
  | other
  /-- `data_in b j e`, of one argument `e`. -/
  | dataIn
  /-- `record_mk` of its arguments, the fields. -/
  | record
  /-- `union_mk` of constructor `pos` (by position), of its arguments, the fields. -/
  | union (pos : Nat)

/-- A pure expression under construction. -/
inductive Atom where
  /-- A variable bound by the output, at level `l` (`l` binders outside it). -/
  | lvl (l : Nat)
  /-- Variable `i` of the enclosing context. -/
  | free (i : Nat)
  /-- A closed trivial introduction form (a literal, a constructor of an enum). -/
  | leaf (stx : Lean.Term)
  /-- The literal `true` or `false`. -/
  | bool (b : Bool)
  /-- Constructor `i` of an enum, whose syntax is `stx`. -/
  | enumLit (i : Nat) (stx : Lean.Term)
  /-- A Lean term of type `PExpr Δ Γ τ` in the enclosing context; `poly` when it is generic
      in the context (then it is used as it is, at any depth).  Of unknown shape: never
      neutral. -/
  | embed (stx : Lean.Term) (poly : Bool)
  /-- A Lean term of type `Neu Δ Γ τ` in the enclosing context (`poly` as for `embed`). -/
  | embedNeu (stx : Lean.Term) (poly : Bool)
  /-- An introduction form (or a pure expression of unknown shape) built from pure
      expressions: `mk` gives its syntax (a `PExpr`) from theirs. -/
  | node (tag : Intro) (mk : Array Lean.Term → MetaM Lean.Term) (args : Array Atom)
  /-- A neutral expression built from the neutral expressions `neus` and the pure expressions
      `args`: `mk` gives its syntax (a `Neu`) from theirs (`Neu` syntax for `neus`, `PExpr`
      syntax for `args`).  Every atom of `neus` is neutral (`Atom.isNeutral`). -/
  | neu (mk : Array Lean.Term → Array Lean.Term → MetaM Lean.Term) (neus args : Array Atom)
  /-- A pure expression at a given type. -/
  | ascribe (a : Atom) (ty : Lean.Term)

instance : Inhabited Atom := ⟨.free 0⟩

/-- Is an atom trivial (used in place, never shared)? -/
def Atom.trivial : Atom → Bool
  | .lvl _ | .free _ | .leaf _ | .bool _ | .enumLit .. => true
  | .ascribe a _ => a.trivial
  | _ => false

/-- Is an atom neutral (`Neu`): a variable or a neutral node?  Only a neutral atom may be taken
    apart (the argument of `data_out`, the condition of `cond`, a scrutinee). -/
def Atom.isNeutral : Atom → Bool
  | .lvl _ | .free _ | .neu .. | .embedNeu .. => true
  | .ascribe a _ => a.isNeutral
  | _ => false

/-- The atom without its type ascriptions. -/
def Atom.strip : Atom → Atom
  | .ascribe a _ => a.strip
  | a => a

mutual

/-- The syntax of an atom as a pure expression (`PExpr`), at output depth `d` (the number of
    binders the output has added around it). -/
partial def Atom.render (a : Atom) (d : Nat) : MetaM Lean.Term :=
  match a with
  | .lvl l => pvarStx (d - 1 - l)
  | .free i => pvarStx (i + d)
  | .leaf stx => pure stx
  | .bool true => `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool true)
  | .bool false => `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool false)
  | .enumLit _ stx => pure stx
  | .embed stx poly => if d == 0 || poly then pure stx else `(LeanScript.PExpr.shift $(quote d) $stx)
  | .embedNeu .. => do `(LeanScript.PExpr.neu $(← a.renderNeu d))
  | .node _ mk args => do mk (← args.mapM (·.render d))
  | .neu mk ns args => do
      `(LeanScript.PExpr.neu $(← mk (← ns.mapM (·.renderNeu d)) (← args.mapM (·.render d))))
  | .ascribe a ty => do `(($(← a.render d) : LeanScript.PExpr _ _ $ty))

/-- The syntax of a neutral atom as a neutral expression (`Neu`), at output depth `d`. -/
partial def Atom.renderNeu (a : Atom) (d : Nat) : MetaM Lean.Term :=
  match a with
  | .lvl l => nvarStx (d - 1 - l)
  | .free i => nvarStx (i + d)
  | .embedNeu stx poly => if d == 0 || poly then pure stx else `(LeanScript.Neu.shift $(quote d) $stx)
  | .neu mk ns args => do mk (← ns.mapM (·.renderNeu d)) (← args.mapM (·.render d))
  | .ascribe a ty => do `(($(← a.renderNeu d) : LeanScript.Neu _ _ $ty))
  | _ => throwError "internal error of the A-normaliser: this pure expression is not neutral"

end

/-- A direct-style source tree.  Variables and join points are de Bruijn indices of the
    source. -/
inductive Src where
  /-- Variable `i`. -/
  | var (i : Nat)
  /-- An atom with no variable of the source (a literal, an embedded Lean term). -/
  | atom (a : Atom)
  /-- An introduction form (or a pure expression of unknown shape) applied to operands. -/
  | pnode (tag : Intro) (mk : Array Lean.Term → MetaM Lean.Term) (args : Array Src)
  /-- A neutral pure expression (`data_out`, `cond`, a cheap extern) applied to operands:
      `neus` are the operands taken apart, which must be neutral, `args` the others.  `red`
      reduces the ι-redex when an operand of `neus` is an introduction form
      (`data_out b j (data_in b j e)` is `e`, `cond true a b` is `a`); an operand of `neus`
      it does not reduce and that is not neutral is shared by a `let` first. -/
  | pneu (mk : Array Lean.Term → Array Lean.Term → MetaM Lean.Term) (neus args : Array Src)
      (red : Array Atom → Array Atom → Option Atom)
  /-- An operand at a given type. -/
  | ascribe (s : Src) (ty : Lean.Term)
  /-- A computation on operands, with bodies (each binding the given number of variables):
      `mk` receives the pure operands and the bodies (statements with no join point). -/
  | comp (mk : Array Lean.Term → Array Lean.Term → MetaM Lean.Term) (args : Array Src)
      (bodies : Array (Nat × Src))
  /-- A Lean term of type `Comp Δ Γ τ` in the enclosing context (`poly`: generic in it). -/
  | embedComp (stx : Lean.Term) (poly : Bool)
  /-- `let x := v; b`. -/
  | letE (v b : Src)
  /-- A non-branching destructuring of a record `scrut`, whose body binds its `n` fields:
      `mk scrut body` (`Term.record_casesOn`, of a neutral `scrut`).  When `scrut` is a record
      literal the body is used with its fields bound (ι-reduction). -/
  | destruct (scrut : Src) (n : Nat) (body : Src) (mk : Lean.Term → Lean.Term → MetaM Lean.Term)
  /-- A branch on `scrut` (`ite`, `enum_casesOn`, `union_casesOn`), one branch per entry
      (binding the given number of variables), whose value has the type `ty?` (when known):
      `mk scrut branches`, of a neutral `scrut`.  `pure?` is its pure form (`Neu.cond`), from
      the scrutinee (neutral) and the branches, when it has one: used when the branch is not in
      tail position and every branch is a pure expression binding nothing.  `sel` recognises a
      scrutinee that is an introduction form: the branch it selects and the atoms of the
      fields that branch binds (ι-reduction). -/
  | cases (ty? : Option Lean.Term) (scrut : Src) (brs : Array (Nat × Src))
      (pure? : Option (Array Lean.Term → Array Lean.Term → MetaM Lean.Term))
      (sel : Atom → Option (Nat × Array Atom))
      (mk : Lean.Term → Array Lean.Term → MetaM Lean.Term)
  /-- `join j (x : ty) := body; main`: `body` binds `x`, `main` sees the join point `j`. -/
  | join (ty? : Option Lean.Term) (body main : Src)
  /-- Jump to join point `j` of the source. -/
  | jump (j : Nat) (arg : Src)
  /-- A Lean term of type `Term Δ Γ τ []` in the enclosing context: in tail position it is the
      statement itself, elsewhere its value is bound by a join point (`Term.retJump`)
      (`poly`: generic in the context). -/
  | embedTerm (stx : Lean.Term) (poly : Bool)

instance : Inhabited Src := ⟨.var 0⟩

/-- What is done with the value of a statement: return it, jump with it to the join point of
    output level `l`, or continue with it. -/
inductive Kont where
  | ret
  | jump (l : Nat)
  | fn (f : Atom → Nat → Nat → MetaM Lean.Term)

/-- The source variables and join points introduced so far, innermost first: the atom each
    variable stands for, the output level of each join point. -/
structure Scope where
  vars : List Atom := []
  joins : List Nat := []

/-- The atom of source variable `i`. -/
def Scope.var (sc : Scope) (i : Nat) : Atom :=
  if h : i < sc.vars.length then sc.vars[i] else .free (i - sc.vars.length)

/-- Bind one more source variable. -/
def Scope.push (sc : Scope) (a : Atom) : Scope := { sc with vars := a :: sc.vars }

/-- Bind source variables to the atoms `as`, the first one innermost (source index `0`). -/
def Scope.pushAll (sc : Scope) (as : List Atom) : Scope := { sc with vars := as ++ sc.vars }

/-- Bind `n` source variables to the output variables of levels `d`, …, `d + n - 1`, the
    last one innermost. -/
def Scope.bindN (sc : Scope) (n : Nat) (d : Nat) : Scope :=
  { sc with vars := ((List.range n).reverse.map fun i => Atom.lvl (d + i)) ++ sc.vars }

/-- The output index of source join point `j` at output join depth `jd`. -/
def Scope.joinIdx (sc : Scope) (j jd : Nat) : Nat :=
  if h : j < sc.joins.length then jd - 1 - sc.joins[j] else j - sc.joins.length + jd

/-- `stx` (a Lean term of the enclosing context) under `d` more binders; as it is when it is
    generic in the context (`poly`). -/
def shiftStx (layer : Name) (stx : Lean.Term) (d : Nat) (poly : Bool) : MetaM Lean.Term :=
  if d == 0 || poly then pure stx else
    `($(mkIdent (`LeanScript ++ layer ++ `shift)) $(quote d) $stx)

/-- Give the answer `a` to the continuation `k`. -/
def Kont.apply (k : Kont) (a : Atom) (d jd : Nat) : MetaM Lean.Term := do
  match k with
  | .ret => `(LeanScript.Term.ret $(← a.render d))
  | .jump l => `(LeanScript.Term.jump $(← dbStx (jd - 1 - l)) $(← a.render d))
  | .fn f => f a d jd

/-- Bind an atom by a source `let`: in place when trivial, else shared. -/
def bindAtom (a : Atom) (d jd : Nat) (k : Atom → Nat → Nat → MetaM Lean.Term) :
    MetaM Lean.Term := do
  if a.trivial then k a d jd
  else `(LeanScript.Term.letE (LeanScript.Comp.share $(← a.render d)) $(← k (.lvl d) (d + 1) jd))

/-- Bind atoms in order (`bindAtom`), then continue with the atoms that stand for them. -/
def bindAtoms (as : List Atom) (d jd : Nat) (k : List Atom → Nat → Nat → MetaM Lean.Term) :
    MetaM Lean.Term :=
  match as with
  | [] => k [] d jd
  | a :: as => bindAtom a d jd fun a d jd => bindAtoms as d jd fun as d jd => k (a :: as) d jd

/-- Make an atom neutral, to take it apart: a neutral atom as it is, any other one (an
    introduction form that no ι-reduction applies to, an embedded Lean term) shared by a
    `let`, whose variable is neutral. -/
def neutral (a : Atom) (d jd : Nat) (k : Atom → Nat → Nat → MetaM Lean.Term) :
    MetaM Lean.Term := do
  if a.isNeutral then k a d jd
  else `(LeanScript.Term.letE (LeanScript.Comp.share $(← a.render d)) $(← k (.lvl d) (d + 1) jd))

/-- `neutral` on each atom, in order. -/
def neutrals (as : List Atom) (d jd : Nat) (k : List Atom → Nat → Nat → MetaM Lean.Term) :
    MetaM Lean.Term :=
  match as with
  | [] => k [] d jd
  | a :: as => neutral a d jd fun a d jd => neutrals as d jd fun as d jd => k (a :: as) d jd

/-- The fields of a record literal (ι-reduction of `record_casesOn`), when the atom is one of
    `n` fields. -/
def Atom.recordFields? (a : Atom) (n : Nat) : Option (List Atom) :=
  match a.strip with
  | .node .record _ args => if args.size == n then some args.toList else none
  | _ => none

/-- The atom of a source tree that is a pure expression as it is: no computation, no binder,
    no `let` needed to take a value apart, and no branch but pure conditionals (`Src.cases`
    with a pure form whose branches are all pure). -/
partial def pureAtom? (s : Src) (sc : Scope) : Option Atom :=
  match s with
  | .var i => some (sc.var i)
  | .atom a => some a
  | .pnode tag mk args => do return .node tag mk (← args.mapM (pureAtom? · sc))
  | .pneu mk neus args red => do
      let ns ← neus.mapM (pureAtom? · sc)
      let as ← args.mapM (pureAtom? · sc)
      match red ns as with
      | some a => return a
      | none =>
          guard (ns.all (·.isNeutral))
          return .neu mk ns as
  | .ascribe s ty => do return .ascribe (← pureAtom? s sc) ty
  | .cases ty? scrut brs (some mkP) sel _ => do
      guard (brs.all (·.1 == 0))
      let c ← pureAtom? scrut sc
      let bs ← brs.mapM (pureAtom? ·.2 sc)
      let a ← match sel c.strip with
        | some (i, _) => bs[i]?
        | none => do guard c.isNeutral; pure (Atom.neu mkP #[c] bs)
      return match ty? with | some ty => .ascribe a ty | none => a
  | _ => none

/-- The branches of a branch that is not in tail position, as pure atoms, when it has a pure
    form and all its branches are pure expressions binding nothing. -/
def pureBranches? (s : Src) (sc : Scope) :
    Option ((Array Lean.Term → Array Lean.Term → MetaM Lean.Term) × Array Atom) :=
  match s with
  | .cases _ _ brs (some mkP) _ _ =>
      if !brs.all (·.1 == 0) then none else
      match brs.mapM (pureAtom? ·.2 sc) with
      | some bs => some (mkP, bs)
      | none => none
  | _ => none

mutual

/-- Normalise the operands `ss` in order, then continue with their atoms. -/
partial def values (ss : List Src) (sc : Scope) (d jd : Nat)
    (k : List Atom → Nat → Nat → MetaM Lean.Term) : MetaM Lean.Term :=
  match ss with
  | [] => k [] d jd
  | s :: ss => value s sc d jd fun a d jd => values ss sc d jd fun as d jd => k (a :: as) d jd

/-- Normalise `s` to an atom, and continue with it. -/
partial def value (s : Src) (sc : Scope) (d jd : Nat) (k : Atom → Nat → Nat → MetaM Lean.Term) :
    MetaM Lean.Term :=
  match s with
  | .var i => k (sc.var i) d jd
  | .atom a => k a d jd
  | .pnode tag mk args => values args.toList sc d jd fun as d jd => k (.node tag mk as.toArray) d jd
  | .pneu mk neus args red => values neus.toList sc d jd fun ns d jd =>
      values args.toList sc d jd fun as d jd =>
        match red ns.toArray as.toArray with
        | some a => k a d jd
        | none => neutrals ns d jd fun ns d jd => k (.neu mk ns.toArray as.toArray) d jd
  | .ascribe s ty => value s sc d jd fun a d jd => k (.ascribe a ty) d jd
  | .comp mk args bodies => values args.toList sc d jd fun as d jd => do
      let ras ← as.toArray.mapM (·.render d)
      let rbs ← bodies.mapM fun (n, b) => stmt b ({ sc with joins := [] }.bindN n d) (d + n) 0 .ret
      let c ← mk ras rbs
      `(LeanScript.Term.letE $c $(← k (.lvl d) (d + 1) jd))
  | .embedComp stx poly => do
      `(LeanScript.Term.letE $(← shiftStx `Comp stx d poly) $(← k (.lvl d) (d + 1) jd))
  | .letE v b => value v sc d jd fun a d jd => bindAtom a d jd fun a d jd => value b (sc.push a) d jd k
  | .destruct scrut n body mk => value scrut sc d jd fun a d jd =>
      match a.recordFields? n with
      | some fs => bindAtoms fs d jd fun fs d jd => value body (sc.pushAll fs) d jd k
      | none => neutral a d jd fun a d jd => do
          mk (← a.renderNeu d) (← value body (sc.bindN n d) (d + n) jd k)
  | .cases ty? scrut brs _ sel mk =>
      match pureBranches? s sc with
      | some (mkP, bs) => value scrut sc d jd fun c d jd =>
          match sel c.strip with
          | some (i, _) => k bs[i]! d jd
          | none => neutral c d jd fun c d jd =>
              let a := Atom.neu mkP #[c] bs
              k (match ty? with | some ty => .ascribe a ty | none => a) d jd
      | none => value scrut sc d jd fun a d jd =>
          match sel a.strip with
          | some (i, fs) => bindAtoms fs.toList d jd fun fs d jd => value brs[i]!.2 (sc.pushAll fs) d jd k
          | none => do
              let body ← k (.lvl d) (d + 1) jd
              let main ← casesAt a brs mk sc d (jd + 1) (.jump jd)
              let ty ← match ty? with | some t => pure t | none => `(_)
              `(LeanScript.Term.join $ty $body $main)
  | .join .. => reify none s sc d jd k
  | .embedTerm stx poly => do
      let body ← k (.lvl d) (d + 1) jd
      `(LeanScript.Term.join _ $body (LeanScript.Term.retJump $(← shiftStx `Term stx d poly)))
  | .jump .. => stmt s sc d jd .ret

/-- The statement `s` whose value is continued with `k`, as a join point for `k` and `s` with
    its value jumping to it. -/
partial def reify (ty? : Option Lean.Term) (s : Src) (sc : Scope) (d jd : Nat)
    (k : Atom → Nat → Nat → MetaM Lean.Term) : MetaM Lean.Term := do
  let body ← k (.lvl d) (d + 1) jd
  let main ← stmt s sc d (jd + 1) (.jump jd)
  let ty ← match ty? with | some t => pure t | none => `(_)
  `(LeanScript.Term.join $ty $body $main)

/-- A branch on the atom `a` (not an introduction form its `sel` recognises), in tail position:
    `a` is made neutral, and each branch goes to `K`. -/
partial def casesAt (a : Atom) (brs : Array (Nat × Src))
    (mk : Lean.Term → Array Lean.Term → MetaM Lean.Term) (sc : Scope) (d jd : Nat) (K : Kont) :
    MetaM Lean.Term :=
  neutral a d jd fun a d jd => do
    mk (← a.renderNeu d) (← brs.mapM fun (n, b) => stmt b (sc.bindN n d) (d + n) jd K)

/-- Normalise `s` to a statement whose value goes to `K`. -/
partial def stmt (s : Src) (sc : Scope) (d jd : Nat) (K : Kont) : MetaM Lean.Term :=
  match s with
  | .letE v b => value v sc d jd fun a d jd => bindAtom a d jd fun a d jd => stmt b (sc.push a) d jd K
  | .destruct scrut n body mk => value scrut sc d jd fun a d jd =>
      match a.recordFields? n with
      | some fs => bindAtoms fs d jd fun fs d jd => stmt body (sc.pushAll fs) d jd K
      | none => neutral a d jd fun a d jd => do
          mk (← a.renderNeu d) (← stmt body (sc.bindN n d) (d + n) jd K)
  | .cases _ scrut brs _ sel mk =>
      match K with
      | .fn f => value s sc d jd f
      | _ => value scrut sc d jd fun a d jd =>
          match sel a.strip with
          | some (i, fs) => bindAtoms fs.toList d jd fun fs d jd => stmt brs[i]!.2 (sc.pushAll fs) d jd K
          | none => casesAt a brs mk sc d jd K
  | .join ty? body main =>
      match K with
      | .fn f => reify none s sc d jd f
      | _ => do
          let ty ← match ty? with | some t => pure t | none => `(_)
          let b ← stmt body (sc.push (.lvl d)) (d + 1) jd K
          let m ← stmt main { sc with joins := jd :: sc.joins } d (jd + 1) K
          `(LeanScript.Term.join $ty $b $m)
  | .jump j arg => value arg sc d jd fun a d jd => do
      `(LeanScript.Term.jump $(← dbStx (sc.joinIdx j jd)) $(← a.render d))
  | .embedTerm stx poly =>
      match K with
      | .ret => if jd == 0 then shiftStx `Term stx d poly else value s sc d jd K.apply
      | _ => value s sc d jd K.apply
  | .comp mk args bodies =>
      match K with
      | .ret => values args.toList sc d jd fun as d _ => do
          let ras ← as.toArray.mapM (·.render d)
          let rbs ← bodies.mapM fun (n, b) =>
            stmt b ({ sc with joins := [] }.bindN n d) (d + n) 0 .ret
          `(LeanScript.Term.ofComp $(← mk ras rbs))
      | _ => value s sc d jd K.apply
  | .embedComp stx poly =>
      match K with
      | .ret => do `(LeanScript.Term.ofComp $(← shiftStx `Comp stx d poly))
      | _ => value s sc d jd K.apply
  | _ => value s sc d jd K.apply

end

/-- Unfold the `Term.ofComp`s the normaliser writes (once the term is elaborated). -/
def unfoldOfComp (e : Expr) : CoreM Expr :=
  Meta.deltaExpand e (· == ``LeanScript.Term.ofComp)

/-- The syntax of the statement (`Term Δ Γ τ js`) that a source tree denotes. -/
def Src.toTerm (s : Src) : MetaM Lean.Term := stmt s {} 0 0 .ret

/-- The syntax of the pure expression (`PExpr Δ Γ τ`) that a source tree denotes; fails when
    it needs a computation or a branch. -/
def Src.toPExpr (s : Src) : MetaM Lean.Term :=
  value s {} 0 0 fun a d jd => do
    unless d == 0 && jd == 0 do
      throwError "this term is not a pure expression: it makes a call, binds or branches"
    a.render 0

/-- The syntax of the neutral expression (`Neu Δ Γ τ`) that a source tree denotes; fails when
    it needs a computation or a branch, or is not neutral. -/
def Src.toNeu (s : Src) : MetaM Lean.Term :=
  value s {} 0 0 fun a d jd => do
    unless d == 0 && jd == 0 && a.isNeutral do
      throwError "this term is not a neutral pure expression: it makes a call, binds, \
        branches, or is a literal or a constructor"
    a.renderNeu 0

/-- The syntax of the computation (`Comp Δ Γ τ`) that a source tree denotes: a computation on
    pure operands, or a pure expression (shared). -/
def Src.toComp (s : Src) : MetaM Lean.Term := do
  match s with
  | .comp mk args bodies => do
      let as ← args.mapM Src.toPExpr
      let bs ← bodies.mapM fun (n, b) => stmt b (({} : Scope).bindN n 0) n 0 .ret
      mk as bs
  | .embedComp stx _ => pure stx
  | s => do `(LeanScript.Comp.share $(← s.toPExpr))

/-! ## Building source trees -/

namespace Src

/-- An application of a function value. -/
def app (f a : Src) : Src :=
  .comp (fun as _ => `(LeanScript.Comp.app $(as[0]!) $(as[1]!))) #[f, a] #[]

/-- `f a₁ … aₙ`. -/
def apps (f : Src) (as : Array Src) : Src := as.foldl app f

/-- `fun x => body` (`ty?` the type of `x`, when given). -/
def lam (ty? : Option Lean.Term) (body : Src) : Src :=
  .comp (fun _ bs => match ty? with
      | some τ => `(LeanScript.Comp.lam (σ := $τ) $(bs[0]!))
      | none => `(LeanScript.Comp.lam $(bs[0]!)))
    #[] #[(1, body)]

/-- A literal `PExpr.lit p v`. -/
def lit (p v : Lean.Term) : MetaM Src := do
  return .atom (.leaf (← `(LeanScript.PExpr.lit $p $v)))

/-- The literal `true` or `false`. -/
def boolLit (b : Bool) : Src := .atom (.bool b)

/-- One layer in. -/
def dataIn (b j : Lean.Term) (e : Src) : Src :=
  .pnode .dataIn (fun xs => `(LeanScript.PExpr.data_in $b $j $(xs[0]!))) #[e]

/-- One layer out: `data_out` of a neutral value; of `data_in b j e` it is `e` (ι-reduction),
    of any other introduction form the value is shared first. -/
def dataOut (b j : Lean.Term) (e : Src) : Src :=
  .pneu (fun ns _ => `(LeanScript.Neu.data_out $b $j $(ns[0]!))) #[e] #[]
    fun ns _ => match ns[0]!.strip with
      | .node .dataIn _ #[x] => some x
      | _ => none

/-- The branch a literal `true`/`false` selects (`true` the first). -/
def boolSel : Atom → Option (Nat × Array Atom)
  | .bool true => some (0, #[])
  | .bool false => some (1, #[])
  | _ => none

/-- The pure conditional `cond c a b` (both branches pure): `Neu.cond` of a neutral `c`; of a
    literal it is the branch (ι-reduction). -/
def cond (c a b : Src) : Src :=
  .pneu (fun ns as => `(LeanScript.Neu.cond $(ns[0]!) $(as[0]!) $(as[1]!))) #[c] #[a, b]
    fun ns as => match boolSel ns[0]!.strip with
      | some (i, _) => as[i]?
      | none => none

/-- `if c then a else b`, of type `ty?`: `Term.ite` in tail position, the pure conditional
    `Neu.cond` elsewhere when both branches are pure, else a join point; the branch itself
    when `c` is a literal. -/
def ite (ty? : Option Lean.Term) (c a b : Src) : Src :=
  .cases ty? c #[(0, a), (0, b)]
    (some fun ns as => `(LeanScript.Neu.cond $(ns[0]!) $(as[0]!) $(as[1]!)))
    boolSel
    fun c bs => `(LeanScript.Term.ite $c $(bs[0]!) $(bs[1]!))

/-- The branches of a union's case analysis. -/
def branchesStx : List Lean.Term → MetaM Lean.Term
  | [a, b] => `(LeanScript.Branches.two $a $b)
  | a :: rest => do `(LeanScript.Branches.cons $a $(← branchesStx rest))
  | [] => throwError "a union has at least two constructors"

/-- The branch and the fields a constructor of a union selects, among branches binding
    `brs`. -/
def unionSel (brs : Array Nat) : Atom → Option (Nat × Array Atom)
  | .node (.union pos) _ args => if brs[pos]? == some args.size then some (pos, args) else none
  | _ => none

/-- The case analysis of a union, one branch per constructor (binding its fields). -/
def unionCases (ty? : Option Lean.Term) (scrut : Src) (brs : Array (Nat × Src)) : Src :=
  .cases ty? scrut brs none (unionSel (brs.map (·.1))) fun c bs => do
    `(LeanScript.Term.union_casesOn $c $(← branchesStx bs.toList))

/-- Take a record of `n` fields apart. -/
def recordCases (scrut : Src) (n : Nat) (body : Src) : Src :=
  .destruct scrut n body fun p b => `(LeanScript.Term.record_casesOn $p $b)

/-- A record from its fields. -/
def recordMk (args : Array Src) : Src :=
  .pnode .record (fun xs => do
    let mut r ← `(LeanScript.Args.nil)
    for x in xs.reverse do r ← `(LeanScript.Args.cons $x $r)
    `(LeanScript.PExpr.record_mk $r)) args

/-- A constructor of a union (`ix` a `CtorIx`, at position `pos` when known) from its
    fields. -/
def unionMk (pos? : Option Nat) (ix : Lean.Term) (args : Array Src) : Src :=
  .pnode (match pos? with | some p => .union p | none => .other) (fun xs => do
    let mut r ← `(LeanScript.Args.nil)
    for x in xs.reverse do r ← `(LeanScript.Args.cons $x $r)
    `(LeanScript.PExpr.union_mk $ix $r)) args

/-- An array literal. -/
def arrayMk (es : Array Src) : Src :=
  .pnode .other (fun xs => do
    let mut r ← `(LeanScript.Elems.nil)
    for x in xs.reverse do r ← `(LeanScript.Elems.cons $x $r)
    `(LeanScript.PExpr.array_mk $r)) es

/-- `Nat.rec`: the step binds the answer (`#0`) and the predecessor (`#1`). -/
def natRec (τ? : Option Lean.Term) (n z s : Src) : Src :=
  .comp (fun xs bs => match τ? with
      | some τ => `(LeanScript.Comp.nat_rec (τ := $τ) $(xs[0]!) $(xs[1]!) $(bs[0]!))
      | none => `(LeanScript.Comp.nat_rec $(xs[0]!) $(xs[1]!) $(bs[0]!)))
    #[n, z] #[(2, s)]

/-- `Array.foldl`: the step binds the element (`#0`) and the accumulator (`#1`). -/
def arrayFoldl (arr z s : Src) : Src :=
  .comp (fun xs bs => `(LeanScript.Comp.array_foldl $(xs[0]!) $(xs[1]!) $(bs[0]!)))
    #[arr, z] #[(2, s)]

/-- A memoised delay of `e` (contents `τ`). -/
def thunkMk (τ : Lean.Term) (e : Src) : Src :=
  .comp (fun _ bs => `(LeanScript.Comp.thunk_mk (τ := $τ) $(bs[0]!))) #[] #[(0, e)]

/-- The value a memoised delay holds (contents `τ`). -/
def thunkForce (τ : Lean.Term) (e : Src) : Src :=
  .comp (fun xs _ => `(LeanScript.Comp.thunk_force (τ := $τ) $(xs[0]!))) #[e] #[]

/-- A lazy delay of `e` (contents `τ`). -/
def lazyMk (τ : Lean.Term) (e : Src) : Src :=
  .comp (fun _ bs => `(LeanScript.Comp.lazy_mk (τ := $τ) $(bs[0]!))) #[] #[(0, e)]

/-- The value a lazy delay holds (contents `τ`). -/
def lazyForce (τ : Lean.Term) (e : Src) : Src :=
  .comp (fun xs _ => `(LeanScript.Comp.lazy_force (τ := $τ) $(xs[0]!))) #[e] #[]

end Src

end LeanScript.Anf

end
