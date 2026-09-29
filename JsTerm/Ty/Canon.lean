module

public import JsTerm.Ty.DecEq

@[expose] public section

set_option autoImplicit false

/-!
# Canonical layout ids (proposal R of `proposals/TypedDataProposals3.md`)

The declared datatypes of a program are rows of a table (`bodies[i]`: the body of datatype `i`,
one layer, whose recursive positions are `obj (decl j) []`).  Read as an automaton — the states
are the datatypes, a state's label is its body with the recursive positions as edges — the
table is **minimised** by partition refinement (`refineClasses`): two datatypes end in one
class when their layouts are equal as infinite trees, and every datatype is mapped to the least
datatype of its class (`canonDecls`).  So `MyList Nat`, a `Stack` with the same constructors,
and every other datatype of the same layout get **one** object id, and equality of object types
stays a comparison of ids.

The answer is checked (`isBisim`: every datatype's body, its recursive positions read as their
canonical ids, is the body of its canonical datatype read the same way); when the check fails
(it cannot) every datatype is its own.  So the answer is always sound:
`canonDecls_sound` proves that a datatype and its canonical datatype unfold to the same layout
at every depth (`JsTy.unfoldDecls`), i.e. they are equal as infinite trees.
-/

namespace MoreJs

mutual
/-- The type with every declaration `obj (decl j) args` it names replaced by `g j`. -/
def JsTy.substDecl (g : Nat → JsTy) : JsTy → JsTy
  | .terminal t => .terminal t
  | .array e => .array (e.substDecl g)
  | .typedArray e => .typedArray e
  | .list e => .list (e.substDecl g)
  | .fn ds c => .fn (JsTy.substDecls g ds) (c.substDecl g)
  | .enum n s => .enum n s
  | .thunk t => .thunk (t.substDecl g)
  | .obj (.decl j) _ => g j
  | .obj (.record n) args => .obj (.record n) (JsTy.substDecls g args)
  | .obj (.union ar r) args => .obj (.union ar r) (JsTy.substDecls g args)
  | .obj .consList args => .obj .consList (JsTy.substDecls g args)
/-- `JsTy.substDecl` of every type of a list. -/
def JsTy.substDecls (g : Nat → JsTy) : List JsTy → List JsTy
  | [] => []
  | t :: ts => t.substDecl g :: JsTy.substDecls g ts
end

mutual
/-- Substituting twice is substituting once, by the substituted substitution. -/
theorem JsTy.substDecl_substDecl (f g : Nat → JsTy) : (t : JsTy) →
    (t.substDecl f).substDecl g = t.substDecl (fun j => (f j).substDecl g)
  | .terminal _ | .typedArray _ | .enum _ _ | .obj (.decl _) _ => by simp [JsTy.substDecl]
  | .array e => by simp [JsTy.substDecl, JsTy.substDecl_substDecl f g e]
  | .list e => by simp [JsTy.substDecl, JsTy.substDecl_substDecl f g e]
  | .thunk e => by simp [JsTy.substDecl, JsTy.substDecl_substDecl f g e]
  | .fn ds c => by
    simp [JsTy.substDecl, JsTy.substDecls_substDecls f g ds, JsTy.substDecl_substDecl f g c]
  | .obj (.record _) args => by simp [JsTy.substDecl, JsTy.substDecls_substDecls f g args]
  | .obj (.union _ _) args => by simp [JsTy.substDecl, JsTy.substDecls_substDecls f g args]
  | .obj .consList args => by simp [JsTy.substDecl, JsTy.substDecls_substDecls f g args]
/-- `JsTy.substDecl_substDecl` on lists. -/
theorem JsTy.substDecls_substDecls (f g : Nat → JsTy) : (ts : List JsTy) →
    JsTy.substDecls g (JsTy.substDecls f ts) = JsTy.substDecls (fun j => (f j).substDecl g) ts
  | [] => by simp [JsTy.substDecls]
  | t :: ts => by
    simp [JsTy.substDecls, JsTy.substDecl_substDecl f g t, JsTy.substDecls_substDecls f g ts]
end

/-- Substitutions that agree give the same type. -/
theorem JsTy.substDecl_congr {f g : Nat → JsTy} (h : ∀ j, f j = g j) (t : JsTy) :
    t.substDecl f = t.substDecl g := by
  have : f = g := funext h
  subst this; rfl

/-- The body of datatype `i` of the table (a placeholder past its end). -/
def bodyAt (bodies : Array JsTy) (i : Nat) : JsTy := bodies[i]?.getD default

/-- The layout of `t` unfolded `n` times through the table: every declaration `decl j` replaced
    by the body of `j` unfolded `n - 1` times, and the declarations left at depth `n` cut (by a
    fixed placeholder).  Two datatypes whose unfoldings agree at every depth have layouts equal
    as infinite trees. -/
def JsTy.unfoldDecls (bodies : Array JsTy) : Nat → JsTy → JsTy
  | 0, t => t.substDecl fun _ => .obj (.decl 0) []
  | n + 1, t => t.substDecl fun j => JsTy.unfoldDecls bodies n (bodyAt bodies j)

/-- The canonical id of datatype `i` under the classes `cls` (itself past the end of `cls`). -/
def classOf (cls : Array Nat) (i : Nat) : Nat := cls.getD i i

/-- The key of datatype `i` under the classes `cls`: its body with every recursive position
    read as its class. -/
def canonKey (bodies : Array JsTy) (cls : Array Nat) (i : Nat) : JsTy :=
  (bodyAt bodies i).substDecl fun j => .obj (.decl (classOf cls j)) []

/-- Are the classes `cls` a bisimulation: is the key of every datatype the key of its
    canonical datatype?  (A datatype past the end of `cls` is its own.) -/
def isBisim (bodies : Array JsTy) (cls : Array Nat) : Bool :=
  (List.range cls.size).all fun i => decide (canonKey bodies cls i = canonKey bodies cls (classOf cls i))

/-- Partition refinement (Hopcroft's minimisation, in its simple quadratic form): every class
    starts as one; a round splits a class by the keys of its members (their recursive positions
    read as classes), each member mapped to the least member of its new class; at most one round
    per datatype, until nothing splits. -/
def refineClasses (bodies : Array JsTy) : Array Nat := Id.run do
  let n := bodies.size
  let mut cls : Array Nat := Array.replicate n 0
  for _ in [0:n + 1] do
    let new := (Array.range n).map fun i =>
      ((List.range n).find? fun k =>
        cls[k]? == cls[i]? && decide (canonKey bodies cls k = canonKey bodies cls i)).getD i
    if new == cls then break
    cls := new
  return cls

/-- **Canonical layout ids**: each datatype mapped to the least datatype whose layout is equal
    to its own as an infinite tree (`refineClasses`), when the classes pass the check
    (`isBisim`); otherwise (it cannot happen) every datatype is its own (`#[]`). -/
def canonDecls (bodies : Array JsTy) : Array Nat :=
  let cls := refineClasses bodies
  if isBisim bodies cls then cls else #[]

/-- The declaration substituted by the unfolding at depth `n`. -/
private def unfoldSubst (bodies : Array JsTy) : Nat → Nat → JsTy
  | 0, _ => .obj (.decl 0) []
  | n + 1, j => JsTy.unfoldDecls bodies n (bodyAt bodies j)

private theorem unfoldDecls_eq (bodies : Array JsTy) (n : Nat) (t : JsTy) :
    JsTy.unfoldDecls bodies n t = t.substDecl (unfoldSubst bodies n) := by
  cases n <;> rfl

/-- **The classes of a bisimulation are sound**: under classes that pass the check, a datatype
    and its canonical datatype unfold to the same layout at every depth. -/
theorem isBisim_sound (bodies : Array JsTy) (cls : Array Nat) (h : isBisim bodies cls = true) :
    ∀ (n i : Nat), JsTy.unfoldDecls bodies n (.obj (.decl i) []) =
      JsTy.unfoldDecls bodies n (.obj (.decl (classOf cls i)) []) := by
  -- the check at every datatype (trivial past the end of `cls`)
  have hk : ∀ i, canonKey bodies cls i = canonKey bodies cls (classOf cls i) := by
    intro i
    by_cases hi : i < cls.size
    · simp only [isBisim, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
      exact h i hi
    · have : classOf cls i = i := by simp [classOf, Array.getD, hi]
      rw [this]
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    show JsTy.unfoldDecls bodies n (bodyAt bodies i) =
      JsTy.unfoldDecls bodies n (bodyAt bodies (classOf cls i))
    -- the unfolding at depth `n` only sees the classes of the declarations
    have hsub : ∀ j, unfoldSubst bodies n j =
        (JsTy.obj (.decl (classOf cls j)) []).substDecl (unfoldSubst bodies n) := by
      intro j
      have := ih j
      simp only [unfoldDecls_eq, JsTy.substDecl] at this
      simpa [JsTy.substDecl] using this
    have hread : ∀ t : JsTy, t.substDecl (unfoldSubst bodies n) =
        (t.substDecl fun j => .obj (.decl (classOf cls j)) []).substDecl (unfoldSubst bodies n) := by
      intro t
      rw [JsTy.substDecl_substDecl]
      exact JsTy.substDecl_congr hsub t
    rw [unfoldDecls_eq, unfoldDecls_eq, hread (bodyAt bodies i), hread (bodyAt bodies (classOf cls i))]
    exact congrArg (JsTy.substDecl (unfoldSubst bodies n)) (hk i)

/-- **Canonical layout ids are sound**: every datatype and the datatype `canonDecls` gives it
    unfold to the same layout at every depth — their layouts are equal as infinite trees, so
    giving them one object id changes nothing the generated JavaScript can observe. -/
theorem canonDecls_sound (bodies : Array JsTy) (n i : Nat) :
    JsTy.unfoldDecls bodies n (.obj (.decl i) []) =
      JsTy.unfoldDecls bodies n (.obj (.decl (classOf (canonDecls bodies) i)) []) := by
  unfold canonDecls
  by_cases h : isBisim bodies (refineClasses bodies) = true
  · simp only [h, ↓reduceIte]
    exact isBisim_sound bodies _ h n i
  · simp [h, classOf]

end MoreJs

end
