module
public import TermTests.RecObjectRecDepthTest
open LeanScript TermTests.RecObjectRecDepth
namespace TermTests.RecObjectRecDepth

abbrev fibStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctorRecord (objF cellSchema)).A)
      (kids : (Ty.toPFunctorRecord (objF cellSchema)).B node → ObjMemo cellSchema natT) =>
    Term.eval envAdd fibBranch (Env.append (objRecEnv cellSchema (by ty_wf) natT 1 node kids) e)
      (by no_rec_mk)

set_option maxHeartbeats 4000000 in
theorem fibStep_cons_cons (e : Env CCtx) (l l' : Nat) (g : Cell) :
    WType.memoFold (fibStep e) (cellVal (.mk l (some (.mk l' (some g))))) =
      WType.memoFold (fibStep e) (cellVal (.mk l' (some g))) +
        WType.memoFold (fibStep e) (cellVal g) := rfl

theorem fib_memoFold (e : Env CCtx) : ∀ c : Cell,
    WType.memoFold (fibStep e) (cellVal c) = Cell.fib c
  | .mk l none => by rw [Cell.fib]; rfl
  | .mk l (some (.mk l' none)) => by rw [Cell.fib]; rfl
  | .mk l (some (.mk l' (some g))) => by
      rw [fibStep_cons_cons, fib_memoFold e (.mk l' (some g)), fib_memoFold e g, Cell.fib]
termination_by c => sizeOf c
decreasing_by all_goals (simp_wf; omega)

theorem fibTerm_correct (c : Cell) : runP fibTerm (cellVal c) = Cell.fib c :=
  fib_memoFold _ c
end TermTests.RecObjectRecDepth
