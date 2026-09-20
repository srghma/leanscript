inductive Fun where
  | Abs : String → Fun → Fun
  | App : Fun → Fun → Fun
  deriving Repr, DecidableEq

/-- One-layer applicative traversal of the immediate children of a node. -/
def traverseFun1 {f : Type → Type} [Applicative f] (k : Fun → f Fun) : Fun → f Fun
  | Fun.Abs id a => Fun.Abs id <$> k a
  | Fun.App a b => Fun.App <$> k a <*> k b

/-- Number of nodes of a term; used as the termination measure. -/
def Fun.size : Fun → Nat
  | Fun.Abs _ a => a.size + 1
  | Fun.App a b => a.size + b.size + 1

/-- Dependent version of `traverseFun1`: the callback is only ever applied to
immediate children, and it is handed a proof that its argument is strictly
smaller than `t`. -/
def traverseFun1D {f : Type → Type} [Applicative f] (t : Fun)
    (k : (a : Fun) → a.size < t.size → f Fun) : f Fun :=
  match t, k with
  | Fun.Abs id a, k => Fun.Abs id <$> k a (by simp [Fun.size])
  | Fun.App a b, k =>
      Fun.App <$> k a (by simp [Fun.size]; omega) <*> k b (by simp [Fun.size]; omega)

/-- Forgetting the size proofs turns `traverseFun1D` back into `traverseFun1`. -/
theorem traverseFun1D_eq {f : Type → Type} [Applicative f] (k : Fun → f Fun) (t : Fun) :
    traverseFun1D t (fun a _ => k a) = traverseFun1 k t := by
  cases t <;> rfl

/-- Bottom-up monadic rewriting: rewrite the children first, then the node. -/
def rewriteBottomUpM {m : Type → Type} [Monad m] (k : Fun → m Fun) (t : Fun) : m Fun := do
  let t' ← traverseFun1D t (fun a _ => rewriteBottomUpM k a)
  k t'
termination_by t.size
decreasing_by exact ‹_›

/-- `rewriteBottomUpM` satisfies the intended recursive equation, phrased with
the original (non-dependent) `traverseFun1`. -/
theorem rewriteBottomUpM_eq {m : Type → Type} [Monad m] (k : Fun → m Fun) (t : Fun) :
    rewriteBottomUpM k t = (do let t' ← traverseFun1 (rewriteBottomUpM k) t; k t') := by
  rw [rewriteBottomUpM, traverseFun1D_eq]

/-- Pure bottom-up rewriting. -/
def rewriteBottomUp (k : Fun → Fun) : Fun → Fun := fun a =>
  Id.run (rewriteBottomUpM (m := Id) (fun f => pure (k f)) a)

/-- The pure version's recursive equation. -/
theorem rewriteBottomUp_eq (k : Fun → Fun) (t : Fun) :
    rewriteBottomUp k t = k (traverseFun1 (f := Id) (rewriteBottomUp k) t) := by
  show Id.run (rewriteBottomUpM (m := Id) (fun f => pure (k f)) t) = _
  rw [rewriteBottomUpM_eq]
  rfl

/-- Unfolding at an `Abs` node. -/
theorem rewriteBottomUp_Abs (k : Fun → Fun) (id : String) (a : Fun) :
    rewriteBottomUp k (Fun.Abs id a) = k (Fun.Abs id (rewriteBottomUp k a)) := by
  rw [rewriteBottomUp_eq]; rfl

/-- Unfolding at an `App` node. -/
theorem rewriteBottomUp_App (k : Fun → Fun) (a b : Fun) :
    rewriteBottomUp k (Fun.App a b) =
      k (Fun.App (rewriteBottomUp k a) (rewriteBottomUp k b)) := by
  rw [rewriteBottomUp_eq]; rfl
