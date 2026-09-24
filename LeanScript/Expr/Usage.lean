module
public import LeanScript.Expr.NatRecCtx

@[expose] public section

set_option autoImplicit false

/-!
# The two indices of an optimized term: its grade vector and its head

`LeanScript.Term` is **optimized by construction**: every constructor that could form a
redex carries a proof that it does not.  For those proofs to be statable *inside* the
inductive, the facts they talk about must be indices of it (a constructor cannot call a
function on the type being defined), and two indices suffice:

* `LeanScript.Usage Γ` — the **grade vector** of a term: how many times each variable of
  `Γ` is used, where a use under a binder that may run many times (a `fun`, a fold
  branch, an unmemoised delay) counts as many (`Usage.many`).  `Term.letE` demands that
  its variable is used at least twice — so a `let` is inlined only where inlining cannot
  duplicate work;
* `LeanScript.Head` — **what the root of a term is**: a variable, a `fun`, a literal, a
  constructor, a closed value (a constructor of literals and closed values), or a
  computation.  `Term.ap` demands that its function is not a `fun` (no β-redex), a
  dispatch on a primitive demands that its scrutinee is not a literal, a dispatch on a
  datatype that its scrutinee is not a constructor, `Term.letE` that its bound
  expression is a computation (or a constructor, whose fields it shares), and an extern
  applied to terms that not all of them are literals or closed values — an extern on
  values is computed where the term is written (`Term.externCall`, and `Term.extern`
  together with `LeanScript.TyWf.quotable`).  The head of a dispatch is computed from the
  heads of its branches (`Head.join`): it is `Head.caseIntro` when a branch is an
  introduction form, and applying or forcing such a dispatch is a redex too — the
  application or the force belongs in the branches.

The grade vector also says whether a fold's branch reads the answers it is given
(`Usage.sumN`): `Term.nat_rec` and `Term.array_rec` ask that it does, since a fold whose
branch reads none of them is a case analysis; and at depth `0` they ask that the branch is
not a variable, since a variable that reads an answer is that answer, and the fold is its
base value.  Likewise a dispatch on a type with one constructor (a record, a newtype, a
primitive wrapper) asks that its branch reads a field (`Usage.front`): there is nothing to
decide, so a branch that reads no field is the whole dispatch.

Both indices are *computed* by the constructors, so writing a term looks exactly like
writing a raw one, and every proof argument is discharged by `decide` on closed indices.
-/

namespace LeanScript

/-- A grade vector: how many times each variable of `Γ` is used. -/
def Usage (Γ : Ctx) : Type := (τ : TyWf) → Var Γ τ → Nat

namespace Usage

variable {Γ : Ctx} {σ : TyWf}

/-- No variable is used. -/
def zero : Usage Γ := fun _ _ => 0

/-- Pointwise sum: the uses of two subterms. -/
def add (u v : Usage Γ) : Usage Γ := fun τ x => u τ x + v τ x

/-- Scaling: the uses of a subterm copied `k` times. -/
def smul (k : Nat) (u : Usage Γ) : Usage Γ := fun τ x => k * u τ x

instance : Zero (Usage Γ) := ⟨zero⟩

instance : Add (Usage Γ) := ⟨add⟩

/-- The uses of a subterm that may **run any number of times**: the body of a `fun`, the
    branch of a fold, an unmemoised delay.  A use there is not one use — the body runs
    once per call, per step, per force — so every use counts as (at least) two, which is
    what `Term.letE` reads as "shared".  Without it, `let x = n * n; fun y => x + y`
    would count `x` as used once, the grammar would reject the `let`, and the only term
    left would be `fun y => n * n + y`, which recomputes `n * n` at every call.

    The grades stay natural numbers: `0` is "unused", `1` is "used exactly once, and
    run at most once", and `≥ 2` is "shared" — which is all that `Term.letE` asks. -/
def many (u : Usage Γ) : Usage Γ := smul 2 u

/-- Extend a grade vector by the grade `k` of a newly bound variable. -/
def cons (k : Nat) (u : Usage Γ) : Usage (σ :: Γ) := fun _ x =>
  match x with
  | .head => k
  | .tail y => u _ y

/-- The grade of the innermost variable. -/
def head (u : Usage (σ :: Γ)) : Nat := u σ .head

/-- Forget the innermost variable. -/
def tail (u : Usage (σ :: Γ)) : Usage Γ := fun τ x => u τ x.tail

/-- The grade vector of a single occurrence of `x`. -/
def single : {Γ : Ctx} → {τ : TyWf} → Var Γ τ → Usage Γ
  | _ :: _, _, .head => cons 1 zero
  | _ :: _, _, .tail x => cons 0 (single x)

/-- The grade vector of `let x = e; b`, where `e` has grades `u` and `b` has grades `v`:
    the uses of `b` except `x`, plus the uses of `e` once per use of `x`.  This is the
    usual graded `let` rule — the grade the term would have after inlining `x`. -/
def letU (u : Usage Γ) (v : Usage (σ :: Γ)) : Usage Γ := smul (head v) u + tail v

/-- Forget the variables a branch binds in front of `Γ`: the fields of a constructor, the
    values of a fold, … (`Δ` is innermost first, as a context is). -/
def drop : (Δ : Ctx) → Usage (Δ ++ Γ) → Usage Γ
  | [], u => u
  | _ :: Δ, u => drop Δ (tail u)

/-- Forget the `n` previous answers a fold binds in front of `Γ` (`LeanScript.natRecCtx`). -/
def dropN (τ : TyWf) : (n : Nat) → Usage (natRecCtx τ n Γ) → Usage Γ
  | 0, u => u
  | n + 1, u => dropN τ n (tail u)

/-- The total grade of the `n` innermost variables of a context `natRecCtx τ n Γ`: how
    many times a fold's branch reads the `n` answers it is given (`Term.nat_rec`,
    `Term.array_rec`).  A fold asks that this is not `0` — a branch that reads none of the
    answers makes the fold a case analysis, which is what it is written as. -/
def sumN (τ : TyWf) : (n : Nat) → Usage (natRecCtx τ n Γ) → Nat
  | 0, _ => 0
  | n + 1, u => head (σ := τ) (Γ := natRecCtx τ n Γ) u + sumN τ n (tail u)

/-- The total grade of the variables `Δ` a branch binds in front of `Γ`: how many times the
    one branch of a dispatch on a type with **one** constructor (a record, a newtype, a
    primitive wrapper such as `Char` or `UInt8`) reads the fields it is given.  Such a
    dispatch asks that this is not `0` (`Term.record_casesOn`, `Term.char_casesOn`, …): a
    branch that reads none of the fields does not need the value taken apart — the
    language is pure and total, so the dispatch is its branch. -/
def front : (Δ : Ctx) → Usage (Δ ++ Γ) → Nat
  | [], _ => 0
  | σ :: Δ, u => head (σ := σ) (Γ := Δ ++ Γ) u + front Δ (tail u)

end Usage

/-- What the root of a term is.  It is an index of `LeanScript.Term`, computed by the
    constructors, and it is what the proofs that a node is not a redex talk about. -/
inductive Head where
  /-- a variable, or a reference to a declaration of the signature: a name, which costs
      nothing to repeat -/
  | var
  /-- a `fun` -/
  | lam
  /-- a literal: a value of a primitive type, or a constructor of an enum -/
  | lit
  /-- a **boolean literal**, whose value the head records: a literal like `Head.lit`, and
      what lets the grammar see that `if c then true else false` is `c`
      (`Term.bool_casesOn`) -/
  | bool (b : Bool)
  /-- a constructor applied to its fields: a record, a tagged value, an array, a delay, a
      value of a recursive type -/
  | ctor
  /-- a computation: an application, a dispatch, a fold or an extern (a `let` has the
      head of its body) -/
  | comp
  /-- a **closed value** that is not a literal: an array whose elements are all literals
      or closed values, or a delay of one.  It is a constructor like `Head.ctor` (a
      dispatch on it, or a force of it, is a redex just the same), but it holds no
      variable and no computation, so its value is known where the term is written: an
      extern called on literals and closed values is a redex too (`Term.externCall`). -/
  | val
  /-- a **dispatch that may answer with an introduction form**: a `match`/`if` at least one
      of whose branches is a `fun`, a literal, a constructor or a closed value — or again
      such a dispatch.  It is a computation like `Head.comp` (a `let` may bind it), but
      what it answers with may be known branch by branch: applying it to an argument
      (`(if c then fun y => b else g) a`) or forcing it (`(if c then thunk e else t).get`)
      is a redex, reduced by moving the application or the force into the branches,
      where it meets the `fun` or the delay (`Term.ap`, `Term.thunk_force`,
      `Term.lazy_force`).  The head of a dispatch is computed from the heads of its
      branches by `Head.join`. -/
  | caseIntro
  /-- a **dispatch that answers with a known constructor in every branch**: a `match`/`if`
      each of whose branches is a literal, a constructor or a closed value — or again such
      a dispatch.  It is a dispatch that may answer with an introduction form
      (`Head.caseIntro`), and more: a dispatch *on* it is a redex (**case-of-case**), since
      in every branch the constructor is known.  `match (if c then some a else none) with
      | some x => f x | none => d` is `if c then f a else d`: the outer dispatch moves into
      the inner branches, where it meets a constructor and is reduced. -/
  | caseCtor
  /-- the head of an **empty list of branches** (`TaggedUnionCasesRest.nil`): never the
      head of a term, it is the neutral element of `Head.join`. -/
  | empty
  deriving DecidableEq, Repr, Inhabited

namespace Head

/-- Is this head a value an extern can be called on where the term is written: a literal
    or a closed value? -/
def isValue : Head → Bool
  | .lit | .bool _ | .val => true
  | _ => false

/-- Is every one of these heads a literal or a closed value?  `Term.externCall` and
    `Term.externCallChecked` ask that not all of their arguments are: a call of an extern
    on values is computed where the term is written — into a literal or a closed value
    when its result type has one (`LeanScript.TyWf.quotable`), and into `Term.extern`
    otherwise. -/
def allValue : List Head → Bool
  | [] => true
  | k :: ks => k.isValue && allValue ks

/-- Is this head a constructor applied to its fields — closed (`Head.val`) or not
    (`Head.ctor`)?  A dispatch on one, or a force of one, is a redex. -/
def isCtor : Head → Bool
  | .ctor | .val => true
  | _ => false

/-- The head of a constructor applied to fields of heads `ks`: a closed value when every
    field is a literal or a closed value, a constructor otherwise. -/
def ctorOf (ks : List Head) : Head := if allValue ks then .val else .ctor

/-- Is this head an introduction form — a `fun`, a literal, a constructor, a closed value —
    or a dispatch that may answer with one (`Head.caseIntro`)? -/
def isIntro : Head → Bool
  | .lam | .lit | .bool _ | .ctor | .val | .caseIntro | .caseCtor => true
  | _ => false

/-- Is this head a **known constructor** — a literal, a constructor applied to its fields,
    a closed value — or a dispatch that answers with one in every branch
    (`Head.caseCtor`)?  A dispatch asks that what it takes apart is not: on a known
    constructor it is a redex, and on a dispatch of known constructors it is one in every
    branch (case-of-case).  (`Head.empty`, which no term has, counts as known, vacuously.) -/
def isKnown : Head → Bool
  | .lit | .bool _ | .ctor | .val | .caseCtor | .empty => true
  | _ => false

/-- The head of a dispatch two of whose branches (or groups of branches) have heads `a`
    and `b`: `Head.caseCtor` when both are known constructors (`Head.isKnown`),
    `Head.caseIntro` when one of them is an introduction form, or such a dispatch, and a
    plain computation `Head.comp` otherwise.  Its value is always one of those three (for a
    non-empty list of branches), so a dispatch is never mistaken for a variable, a `fun` or
    a constructor.  `Head.empty` is its neutral element. -/
def join (a b : Head) : Head :=
  if a.isKnown && b.isKnown then .caseCtor
  else if a.isIntro || b.isIntro then .caseIntro else .comp

/-- Is this head a `fun`, or a dispatch that may answer with one?  `Term.ap` asks that its
    function is neither: the first is a β-redex, and the second is one in some branch,
    reached by applying each branch instead. -/
def isFunLike : Head → Bool
  | .lam | .caseIntro => true
  | _ => false

/-- Is this head a constructor applied to its fields (closed or not), or a dispatch that may
    answer with one?  `Term.thunk_force` and `Term.lazy_force` ask that what they force is
    neither: forcing a delay built right there is a redex, and so is forcing a dispatch
    one of whose branches builds it — the force moves into the branches. -/
def isCtorLike : Head → Bool
  | .ctor | .val | .caseIntro | .caseCtor => true
  | _ => false

end Head

end LeanScript

end
