module
public import LeanScript.Expr.NatRecCtx
public import LeanScript.Expr.Quotable

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

The grade vector also counts, in total, the uses of **free names** — the variables of `Γ`
and the top-level declarations of the signature (`Usage.free`, `Usage.global`).  A term
that uses none is **closed** (`Usage.closed`): its value is known where the term is
written.  So a closed **computation** at a type whose values can be written back as terms
(`Head.closedComp`: an application, a `let` read by a computation, an extern call, a fold,
a force or a dispatch on a type that may hold a function) is a redex, and those
constructors ask that they are not one (`hClosed`): `sumTo 5` must be written `10`, and
`fun x => x + sumTo 4` must be written `fun x => x + 6`.  (A dispatch on a primitive type
or an enum needs no such proof: its scrutinee has a type whose values can be written, so a
closed one is a literal — already rejected — or a closed computation that is itself
rejected.)

Both indices are *computed* by the constructors, so writing a term looks exactly like
writing a raw one, and every proof argument is discharged by `decide` on closed indices.
-/

namespace LeanScript

/-- A grade vector: how many times each variable of `Γ` is used (`count`), together with
    the total number of uses of **free names** (`free`): the variables of `Γ`, and the
    top-level declarations of the signature (`Term.global`).  A term whose `free` is `0`
    reads nothing it is not given — it is **closed** (`Usage.closed`), and its value is
    known where the term is written.

    `free` is computed alongside `count` by every operation below, so that it reduces
    without knowing `Γ`: it is the sum of `count` over `Γ`, plus the uses of declarations
    (`Usage.global`). -/
structure Usage (Γ : Ctx) : Type where
  /-- How many times each variable of `Γ` is used. -/
  count : (τ : TyWf) → Var Γ τ → Nat
  /-- How many times a free name — a variable of `Γ` or a declaration of the signature —
      is used, in total. -/
  free : Nat
  /-- How many times each variable of `Γ`, by de Bruijn index, is **taken apart**: is the
      scrutinee of a dispatch (`Usage.scrutinize`).  A dispatch on a variable asks that
      its branches do not take that variable apart again (`Head.rescrutinizes`): in each
      branch the constructor is known. -/
  scrut : Nat → Nat

namespace Usage

variable {Γ : Ctx} {σ : TyWf}

instance : CoeFun (Usage Γ) (fun _ => (τ : TyWf) → Var Γ τ → Nat) := ⟨Usage.count⟩

/-- No variable is used. -/
def zero : Usage Γ := ⟨fun _ _ => 0, 0, fun _ => 0⟩

/-- Pointwise sum: the uses of two subterms. -/
def add (u v : Usage Γ) : Usage Γ :=
  ⟨fun τ x => u.count τ x + v.count τ x, u.free + v.free, fun i => u.scrut i + v.scrut i⟩

/-- Scaling: the uses of a subterm copied `k` times. -/
def smul (k : Nat) (u : Usage Γ) : Usage Γ :=
  ⟨fun τ x => k * u.count τ x, k * u.free, fun i => k * u.scrut i⟩

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

/-- The grade vector of a reference to a top-level declaration (`Term.global`): no
    variable of `Γ` is used, but a free name is — the term is not closed, since the value
    of the declaration is only known when the term runs. -/
def global : Usage Γ := ⟨fun _ _ => 0, 1, fun _ => 0⟩

/-- Extend a grade vector by the grade `k` of a newly bound variable. -/
def cons (k : Nat) (u : Usage Γ) : Usage (σ :: Γ) :=
  ⟨fun _ x =>
    match x with
    | .head => k
    | .tail y => u.count _ y, k + u.free,
   fun i =>
    match i with
    | 0 => 0
    | i + 1 => u.scrut i⟩

/-- The grade of the innermost variable. -/
def head (u : Usage (σ :: Γ)) : Nat := u.count σ .head

/-- Forget the innermost variable. -/
def tail (u : Usage (σ :: Γ)) : Usage Γ :=
  ⟨fun τ x => u.count τ x.tail, u.free - head u, fun i => u.scrut (i + 1)⟩

/-- The grade vector of a single occurrence of `x`. -/
def single : {Γ : Ctx} → {τ : TyWf} → Var Γ τ → Usage Γ
  | _ :: _, _, .head => cons 1 zero
  | _ :: _, _, .tail x => cons 0 (single x)

/-- The grade vector of `let x = e; b`, where `e` has grades `u` and `b` has grades `v`:
    the uses of `b` except `x`, plus the uses of `e` once per use of `x`.  This is the
    usual graded `let` rule — the grade the term would have after inlining `x`. -/
def letU (u : Usage Γ) (v : Usage (σ :: Γ)) : Usage Γ := smul (head v) u + tail v

/-- Is a term of these grades **closed**: does it use no variable of `Γ` and no top-level
    declaration?  Its value is then known where the term is written. -/
def closed (u : Usage Γ) : Bool := u.free == 0

/-! The number of uses of free names, operation by operation: what the tactic `not_closed`
rewrites with, to see that a term with a variable part is not closed. -/

@[simp] theorem free_zero : (0 : Usage Γ).free = 0 := rfl
@[simp] theorem free_add (u v : Usage Γ) : (u + v).free = u.free + v.free := rfl
@[simp] theorem free_smul (k : Nat) (u : Usage Γ) : (smul k u).free = k * u.free := rfl
@[simp] theorem free_many (u : Usage Γ) : (many u).free = 2 * u.free := rfl
@[simp] theorem free_global : (global : Usage Γ).free = 1 := rfl
@[simp] theorem free_cons (k : Nat) (u : Usage Γ) : (cons (σ := σ) k u).free = k + u.free := rfl
@[simp] theorem free_tail (u : Usage (σ :: Γ)) : (tail u).free = u.free - head u := rfl
@[simp] theorem free_single {τ : TyWf} (x : Var Γ τ) : (single x).free = 1 := by
  induction x with
  | head => rfl
  | tail y ih => show 0 + (single y).free = 1; rw [ih]

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
  /-- the variable of de Bruijn index `i`: a name, which costs nothing to repeat.  The
      head records **which** variable it is, so that the grammar can see that
      `if c then x else x` is `x` (`Term.bool_casesOn`), and that `fun y => f y` applies
      `f` to the variable the `fun` binds (`Head.app`, `Term.lam`). -/
  | var (i : Nat)
  /-- a reference to a declaration of the signature: a name, which costs nothing to
      repeat -/
  | global
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
  /-- an **application** `f a`: a computation like `Head.comp`, which records whether `a`
      is the innermost variable (de Bruijn index `0`) — what lets the grammar see an
      η-redex: `fun x => f x`, where `f` does not read `x`, is `f` (`Term.lam`).  A `let`
      forgets it (`Head.underBinder`): under a `let`, index `0` is the `let`'s variable. -/
  | app (onVar0 : Bool)
  /-- a **closed value** that is not a literal: an array, a record, a tagged value or a
      value of a recursive tagged union whose fields are all literals or closed values,
      or a delay of one.  It is a constructor like `Head.ctor` (a
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

/-- Is this head a **computation** — an application, a fold, an extern, a force, or a
    dispatch (`Head.comp`, `Head.caseIntro`, `Head.caseCtor`) — rather than a name, a `fun`,
    a literal or a constructor? -/
def isComp : Head → Bool
  | .comp | .app _ | .caseIntro | .caseCtor => true
  | _ => false

/-- Is this head a variable (not a reference to a declaration)? -/
def isVar : Head → Bool
  | .var _ => true
  | _ => false

/-- May a `let` bind a term of this head: a computation (whose value it shares) or a
    constructor (whose fields it shares)?  A variable, a `fun` or a literal is inlined:
    binding it saves nothing (`Term.letE`). -/
def isBindable (k : Head) : Bool := k.isComp || k.isCtor

/-- Is this head the innermost variable, de Bruijn index `0`?  An application to it is
    what an η-redex's body is (`Head.app`, `Term.ap`). -/
def isVar0 : Head → Bool
  | .var 0 => true
  | _ => false

/-- The head of a `let` whose body has head `k`: the body's, except that an application to
    the innermost variable is one to the `let`'s variable, which is no longer innermost
    outside it (`Term.letE`). -/
def underBinder : Head → Head
  | .app _ => .app false
  | k => k

/-- Is `fun x => b`, where `b` has head `kb` and reads `x` `n` times, an **η-redex**:
    `b` is `f x` (`Head.app true`), and `x` is read only there — `f` does not read it —
    so the `fun` is `f`?  `Term.lam` asks that it is not. -/
def isEtaRedex : Head → Nat → Bool
  | .app onVar0, n => n == 1 && onVar0
  | _, _ => false

/-- Are these the heads of two terms that are **the same leaf**: the same variable, or the
    same boolean literal?  A dispatch whose branches are the same leaf — `if c then x else
    x`, or `if c then true else true` (what `c || true` is) — is that leaf, the language
    being pure and total (`Term.bool_casesOn`). -/
def sameLeaf : Head → Head → Bool
  | .var i, .var j => i == j
  | .bool a, .bool b => a == b
  | _, _ => false

end Head

/-- The grades of a **dispatch** on a scrutinee of head `k`, whose parts have grades `u`:
    `u`, and when the scrutinee is the variable of de Bruijn index `i` (`Head.var`), one
    more use of `i` **as a scrutinee** (`Usage.scrut`).  This is what lets a dispatch on
    `i` further out see that it is taken apart again in one of its branches. -/
def Usage.scrutinize {Γ : Ctx} (k : Head) (u : Usage Γ) : Usage Γ :=
  match k with
  | .var i => ⟨u.count, u.free, fun j => if j = i then u.scrut j + 1 else u.scrut j⟩
  | _ => u

@[simp] theorem Usage.free_scrutinize {Γ : Ctx} (k : Head) (u : Usage Γ) :
    (Usage.scrutinize k u).free = u.free := by
  cases k <;> rfl

/-- Does a dispatch on a scrutinee of head `k` whose branches have grades `w` take the
    scrutinee apart **again** in a branch: is the scrutinee a variable (`Head.var i`) that
    a dispatch in the branches is on too (`Usage.scrut`)?  That inner dispatch is a
    redex — **case of a known constructor**: in each branch the constructor of `i` is the
    branch's own, and its fields are bound — so a dispatch on a variable asks that this is
    `false`.  `match o with | some x => … (match o with | some y => f y | none => d) …` is
    `match o with | some x => … f x …`. -/
def Head.rescrutinizes {Γ : Ctx} (k : Head) (w : Usage Γ) : Bool :=
  match k with
  | .var i => w.scrut i != 0
  | _ => false

/-- Is a term of grades `u`, type `τ` and head `k` a **closed computation that can be
    written as its value**: a computation (`Head.isComp`) that reads no variable and no
    top-level declaration (`Usage.closed`), at a type whose values can be written back as
    terms (`TyWf.quotable`)?  Its value is known where the term is written, so it is a
    redex, and the grammar rejects it: the computation constructors of `LeanScript.Term`
    ask that this is `false` (`hClosed`), and the translation computes the value instead
    (`sumTo 5` is written `10`, not as a fold on the literal `5`).  A constructor or a `let` of a
    closed value (`let x = #[…]; (x, x)`) is not a computation, so it is not rejected: a
    `let` may share a closed value. -/
def Head.closedComp {Γ : Ctx} (u : Usage Γ) (τ : TyWf) (k : Head) : Bool :=
  u.closed && k.isComp && τ.quotable

end LeanScript

end
