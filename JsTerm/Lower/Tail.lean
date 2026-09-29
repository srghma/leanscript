module

public import JsTerm.Syntax.Vars

@[expose] public section

set_option autoImplicit false

/-!
# The tails of the blocks the conversion builds

Two structural rewrites the conversion from `Term` (`JsTerm.Lower.FromTerm`) needs to build
the shapes of JavaScript it emits (they are not optimisations: the conversion cannot write
these statements otherwise):

* **the end of a loop body** (`JsBlock.retToNext`): the body of a loop is converted from a
  statement that returns the new accumulator; each `return e` becomes `acc = e;` and the end
  of the iteration;
* **returns as jumps** (`JsBlock.retToJump`): each `return e` becomes a jump to a new join
  point (how a block computing a function is applied to more arguments).
-/

namespace MoreJs

variable {S : JsSig}

/-! ## The end of a loop body -/


mutual
/-- Every `return e` of a loop body becomes `acc = e;` and the end of the iteration. -/
partial def JsBlock.retToNext {C M J : List JsTy} {α : JsTy} (acc : JsMem M α) :
    JsBlock S C M J (.ret α) → JsBlock S C M J .loop
  | .ret e => .assign acc e .next
  | .jump j e => .jump j e
  | .throw msg => .throw msg
  | .const x e rest => .const x e (rest.retToNext acc)
  | .letMut x e rest => .letMut x e (rest.retToNext acc.succ)
  | .assign x e rest => .assign x e (rest.retToNext acc)
  | .destructure e sel rest => .destructure e sel (rest.retToNext acc)
  | .ite c t e => .ite c (t.retToNext acc) (e.retToNext acc)
  | .enumCases e arms => .enumCases e (arms.retToNext acc)
  | .unionCases e arms => .unionCases e (arms.retToNext acc)
  | .join x b rest => .join x (b.retToNext acc) (rest.retToNext acc)
  | .forRange x nt n b rest => .forRange x nt n b (rest.retToNext acc)
  | .forOf x l xs b rest => .forOf x l xs b (rest.retToNext acc)
  | .funs xs defs rest => .funs xs defs (rest.retToNext acc)
/-- `retToNext` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.retToNext {C M J : List JsTy} {α : JsTy} {n : Nat} (acc : JsMem M α) :
    JsEnumArms S C M J (.ret α) n → JsEnumArms S C M J .loop n
  | .nil => .nil
  | .cons b rest => .cons (b.retToNext acc) (rest.retToNext acc)
/-- `retToNext` in the arms of a case analysis on a union. -/
partial def JsUnionArms.retToNext {C M J : List JsTy} {α : JsTy} {cs : List (List JsTy)} (acc : JsMem M α) :
    JsUnionArms S C M J (.ret α) cs → JsUnionArms S C M J .loop cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.retToNext acc) (rest.retToNext acc)
end

/-! ## Returns as jumps -/

/-- A position in `J`, in `J ++ K`. -/
def JsMem.appendR {α : Type} {J : List α} {x : α} (K : List α) : JsMem J x → JsMem (J ++ K) x
  | .zero => .zero
  | .succ m => .succ (m.appendR K)

/-- The position of `x` in `J ++ [x]`. -/
def JsMem.last {α : Type} {x : α} : (J : List α) → JsMem (J ++ [x]) x
  | [] => .zero
  | _ :: J => .succ (JsMem.last J)

mutual
/-- Every `return e` of a block becomes a jump passing `e` to a new join point, outside the
    ones of the block (`join x (b.retToJump) rest` computes what `b` returns into `x`, then
    runs `rest`). -/
partial def JsBlock.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} :
    JsBlock S C M J (.ret τ) → JsBlock S C M (J ++ [τ]) k
  | .ret e => .jump (JsMem.last J) e
  | .jump j e => .jump (j.appendR [τ]) e
  | .throw msg => .throw msg
  | .const x e rest => .const x e rest.retToJump
  | .letMut x e rest => .letMut x e rest.retToJump
  | .assign x e rest => .assign x e rest.retToJump
  | .destructure e sel rest => .destructure e sel rest.retToJump
  | .ite c t e => .ite c t.retToJump e.retToJump
  | .enumCases e arms => .enumCases e arms.retToJump
  | .unionCases e arms => .unionCases e arms.retToJump
  | .join x b rest => .join x b.retToJump rest.retToJump
  | .forRange x nt n b rest => .forRange x nt n b rest.retToJump
  | .forOf x l xs b rest => .forOf x l xs b rest.retToJump
  | .funs xs defs rest => .funs xs defs rest.retToJump
/-- `retToJump` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J (.ret τ) n → JsEnumArms S C M (J ++ [τ]) k n
  | .nil => .nil
  | .cons b rest => .cons b.retToJump rest.retToJump
/-- `retToJump` in the arms of a case analysis on a union. -/
partial def JsUnionArms.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd}
    {cs : List (List JsTy)} : JsUnionArms S C M J (.ret τ) cs → JsUnionArms S C M (J ++ [τ]) k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.retToJump rest.retToJump
end

end MoreJs

end
