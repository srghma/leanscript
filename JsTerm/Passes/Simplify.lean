module

public import JsTerm.Syntax.Vars

@[expose] public section

set_option autoImplicit false

/-!
# Clean-ups of the JavaScript grammar

Rewrites of `JsTerm` that make the printed JavaScript shorter, all type-preserving (they map a
`JsBlock C M J k` to a `JsBlock C M J k`):

* **the end of a loop body** (`JsBlock.retToNext`): the body of a loop is converted from a
  statement that returns the new accumulator; each `return e` becomes `acc = e;` and the end
  of the iteration;
* **returns as jumps** (`JsBlock.retToJump`): each `return e` becomes a jump to a new join
  point (how a block computing a function is applied to more arguments, `FromTerm`);
* **peephole** (`peephole`): `const x = e; return x;` is `return e;`, `const x = e; jump j x;`
  is `jump j e;`, and a join point whose block only jumps to it, `let x; L: { x = e; break L; }`,
  is `const x = e;` (one whose block is `if (c) { jump a } else { jump b }` is
  `const x = c ? a : b;`);
* **array literals** (`inlineArrays`): the appends of generic arrays are array literals of
  spreads (`[...a, ...b]`), so a chain of appends is nested literals.  A spread of an array
  literal is its elements (`[x, ...[y, ...z]]` is `[x, y, ...z]`), and `const x = [ … ];` used
  exactly once afterwards, not inside a loop or a closure, is inlined into that use (the
  elements of such a literal are variables, literals and spreads of those: they have no effect
  and cannot fail, so moving the literal is safe as long as none of its mutable variables is
  reassigned in between).

The rewrites are applied bottom-up by one generic traversal (`JsBlock.mapBU`).
-/

namespace MoreJs

/-! ## The end of a loop body -/

mutual
/-- Every `return e` of a loop body becomes `acc = e;` and the end of the iteration. -/
partial def JsBlock.retToNext {C M J : List JsTy} {α : JsTy} (acc : JsMem M α) :
    JsBlock C M J (.ret α) → JsBlock C M J .loop
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
  | .lastIter x nt n b rest => .lastIter x nt n b (rest.retToNext acc)
  | .forOf x l xs b rest => .forOf x l xs b (rest.retToNext acc)
/-- `retToNext` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.retToNext {C M J : List JsTy} {α : JsTy} {n : Nat} (acc : JsMem M α) :
    JsEnumArms C M J (.ret α) n → JsEnumArms C M J .loop n
  | .nil => .nil
  | .cons b rest => .cons (b.retToNext acc) (rest.retToNext acc)
/-- `retToNext` in the arms of a case analysis on a union. -/
partial def JsUnionArms.retToNext {C M J : List JsTy} {α : JsTy} {cs : List (List JsTy)} (acc : JsMem M α) :
    JsUnionArms C M J (.ret α) cs → JsUnionArms C M J .loop cs
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
    JsBlock C M J (.ret τ) → JsBlock C M (J ++ [τ]) k
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
  | .lastIter x nt n b rest => .lastIter x nt n b rest.retToJump
  | .forOf x l xs b rest => .forOf x l xs b rest.retToJump
/-- `retToJump` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms C M J (.ret τ) n → JsEnumArms C M (J ++ [τ]) k n
  | .nil => .nil
  | .cons b rest => .cons b.retToJump rest.retToJump
/-- `retToJump` in the arms of a case analysis on a union. -/
partial def JsUnionArms.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd}
    {cs : List (List JsTy)} : JsUnionArms C M J (.ret τ) cs → JsUnionArms C M (J ++ [τ]) k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.retToJump rest.retToJump
end

/-! ## A bottom-up traversal -/

/-- A rewrite of the expressions of every context. -/
structure JsExprRewrite where
  run : (C M : List JsTy) → (τ : JsTy) → JsExpr C M τ → JsExpr C M τ

/-- A rewrite of the blocks of every context. -/
structure JsBlockRewrite where
  run : (C M J : List JsTy) → (k : JsEnd) → JsBlock C M J k → JsBlock C M J k

mutual
/-- Rewrite an expression bottom-up: its parts first, then itself with `fe` (and every block
    inside it with `fb`). -/
def JsExpr.mapBU (fe : JsExprRewrite) (fb : JsBlockRewrite) {C M : List JsTy} {τ : JsTy} :
    JsExpr C M τ → JsExpr C M τ
  | .cvar x => fe.run _ _ _ (.cvar x)
  | .mvar x => fe.run _ _ _ (.mvar x)
  | .global n t => fe.run _ _ _ (.global n t)
  | .lit l => fe.run _ _ _ (.lit l)
  | .imported op as => fe.run _ _ _ (.imported op (as.mapBU fe fb))
  | .inlined op as => fe.run _ _ _ (.inlined op (as.mapBU fe fb))
  | .unreachable t => fe.run _ _ _ (.unreachable t)
  | .app f as => fe.run _ _ _ (.app (f.mapBU fe fb) (as.mapBU fe fb))
  | .lam xs b => fe.run _ _ _ (.lam xs (b.mapBU fe fb))
  | .record_mk fs => fe.run _ _ _ (.record_mk (fs.mapBU fe fb))
  | .union_mk ix as => fe.run _ _ _ (.union_mk ix (as.mapBU fe fb))
  | .enum_mk n s i => fe.run _ _ _ (.enum_mk n s i)
  | .array_mk l ps => fe.run _ _ _ (.array_mk l (ps.mapBU fe fb))
  | .list_mk ps => fe.run _ _ _ (.list_mk (ps.mapBU fe fb))
  | .cond c a b => fe.run _ _ _ (.cond (c.mapBU fe fb) (a.mapBU fe fb) (b.mapBU fe fb))
/-- `mapBU` of arguments. -/
def JsArgs.mapBU (fe : JsExprRewrite) (fb : JsBlockRewrite) {C M σs : List JsTy} :
    JsArgs C M σs → JsArgs C M σs
  | .nil => .nil
  | .cons a as => .cons (a.mapBU fe fb) (as.mapBU fe fb)
/-- `mapBU` of the parts of an array literal. -/
def JsParts.mapBU (fe : JsExprRewrite) (fb : JsBlockRewrite) {C M : List JsTy} {A E : JsTy} :
    JsParts C M A E → JsParts C M A E
  | .nil => .nil
  | .elem e rest => .elem (e.mapBU fe fb) (rest.mapBU fe fb)
  | .spread a rest => .spread (a.mapBU fe fb) (rest.mapBU fe fb)
/-- Rewrite a block bottom-up: its parts first, then itself with `fb`. -/
def JsBlock.mapBU (fe : JsExprRewrite) (fb : JsBlockRewrite) {C M J : List JsTy} {k : JsEnd} :
    JsBlock C M J k → JsBlock C M J k
  | .ret e => fb.run _ _ _ _ (.ret (e.mapBU fe fb))
  | .next => fb.run _ _ _ _ .next
  | .jump j e => fb.run _ _ _ _ (.jump j (e.mapBU fe fb))
  | .throw msg => fb.run _ _ _ _ (.throw msg)
  | .const x e rest => fb.run _ _ _ _ (.const x (e.mapBU fe fb) (rest.mapBU fe fb))
  | .letMut x e rest => fb.run _ _ _ _ (.letMut x (e.mapBU fe fb) (rest.mapBU fe fb))
  | .assign x e rest => fb.run _ _ _ _ (.assign x (e.mapBU fe fb) (rest.mapBU fe fb))
  | .destructure e sel rest =>
    fb.run _ _ _ _ (.destructure (e.mapBU fe fb) sel (rest.mapBU fe fb))
  | .ite c t e => fb.run _ _ _ _ (.ite (c.mapBU fe fb) (t.mapBU fe fb) (e.mapBU fe fb))
  | .enumCases e arms => fb.run _ _ _ _ (.enumCases (e.mapBU fe fb) (arms.mapBU fe fb))
  | .unionCases e arms => fb.run _ _ _ _ (.unionCases (e.mapBU fe fb) (arms.mapBU fe fb))
  | .join x b rest => fb.run _ _ _ _ (.join x (b.mapBU fe fb) (rest.mapBU fe fb))
  | .forRange x nt n b rest =>
    fb.run _ _ _ _ (.forRange x nt (n.mapBU fe fb) (b.mapBU fe fb) (rest.mapBU fe fb))
  | .lastIter x nt n b rest =>
    fb.run _ _ _ _ (.lastIter x nt (n.mapBU fe fb) (b.mapBU fe fb) (rest.mapBU fe fb))
  | .forOf x l xs b rest =>
    fb.run _ _ _ _ (.forOf x l (xs.mapBU fe fb) (b.mapBU fe fb) (rest.mapBU fe fb))
/-- `mapBU` of the arms of a case analysis on an enum. -/
def JsEnumArms.mapBU (fe : JsExprRewrite) (fb : JsBlockRewrite) {C M J : List JsTy} {k : JsEnd}
    {n : Nat} : JsEnumArms C M J k n → JsEnumArms C M J k n
  | .nil => .nil
  | .cons b rest => .cons (b.mapBU fe fb) (rest.mapBU fe fb)
/-- `mapBU` of the arms of a case analysis on a union. -/
def JsUnionArms.mapBU (fe : JsExprRewrite) (fb : JsBlockRewrite) {C M J : List JsTy} {k : JsEnd}
    {cs : List (List JsTy)} : JsUnionArms C M J k cs → JsUnionArms C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.mapBU fe fb) (rest.mapBU fe fb)
end

/-- The rewrite that changes nothing. -/
def JsExprRewrite.id : JsExprRewrite := ⟨fun _ _ _ e => e⟩

/-- The rewrite that changes nothing. -/
def JsBlockRewrite.id : JsBlockRewrite := ⟨fun _ _ _ _ b => b⟩

/-! ## Peephole -/

/-- `const x = e; return x;` is `return e;`, and `const x = e; jump j x;` is `jump j e;`. -/
def constRule {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | .const _ e (.ret (.cvar .zero)) => .ret e
  | .const _ e (.jump j (.cvar .zero)) => .jump j e
  | b => b

/-- The value a join block computes, when it only jumps to its join point (`jump 0 e`, or
    `if (c) { jump 0 a } else { jump 0 b }`). -/
def joinValue? {C M J : List JsTy} {τ : JsTy} {k : JsEnd} :
    JsBlock C M (τ :: J) k → Option (JsExpr C M τ)
  | .jump .zero e => some e
  | .ite c (.jump .zero a) (.jump .zero b) => some (.cond c a b)
  | _ => none

/-- One peephole step, on a block whose parts are clean already. -/
def peepholeNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | .join x block rest =>
    match joinValue? block with
    | some e => constRule (.const x e rest)
    | none => .join x block rest
  | b => constRule b

/-- The peephole rules, everywhere. -/
def peephole {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  b.mapBU .id ⟨fun _ _ _ _ b => peepholeNode b⟩

/-! ## Array literals -/

/-- The parts of two array literals, one after the other. -/
def JsParts.append {C M : List JsTy} {A E : JsTy} : JsParts C M A E → JsParts C M A E → JsParts C M A E
  | .nil, qs => qs
  | .elem e ps, qs => .elem e (ps.append qs)
  | .spread a ps, qs => .spread a (ps.append qs)

/-- The parts of a list literal, as the parts of an array literal: a list is a JavaScript
    array, so a spread of a list `xs` is the spread of `xs` as an array
    (`array__lean_array_mk`, which is written as its argument). -/
def JsParts.listToArray {C M : List JsTy} {α : JsTy} :
    JsParts C M (.list α) α → JsParts C M (.array α) α
  | .nil => .nil
  | .elem e ps => .elem e ps.listToArray
  | .spread xs ps => .spread (.inlined (.array__lean_array_mk α) (.cons xs .nil)) ps.listToArray

/-- The parts of a generic array literal, as the parts of a list literal (a spread of an
    array `a` is the spread of `a` as a list, `array__lean_array_to_list`, written as its
    argument). -/
def JsParts.arrayToList {C M : List JsTy} {α : JsTy} :
    JsParts C M (.array α) α → JsParts C M (.list α) α
  | .nil => .nil
  | .elem e ps => .elem e ps.arrayToList
  | .spread a ps => .spread (.inlined (.array__lean_array_to_list α) (.cons a .nil)) ps.arrayToList

/-- The parts of a generic array that is a literal: an array literal, or a list literal
    converted to an array (`array__lean_array_mk([ … ])`, the same JavaScript array). -/
def JsExpr.arrayLitParts? {C M : List JsTy} {α : JsTy} :
    JsExpr C M (.array α) → Option (JsParts C M (.array α) α)
  | .array_mk (.generic _) ps => some ps
  | .inlined (.array__lean_array_mk _) (.cons (.list_mk ps) .nil) => some ps.listToArray
  | _ => none

/-- The parts of a list that is a literal: a list literal, or a generic array literal
    converted to a list (`array__lean_array_to_list([ … ])`). -/
def JsExpr.listLitParts? {C M : List JsTy} {α : JsTy} :
    JsExpr C M (.list α) → Option (JsParts C M (.list α) α)
  | .list_mk ps => some ps
  | .inlined (.array__lean_array_to_list _) (.cons (.array_mk (.generic _) ps) .nil) =>
    some ps.arrayToList
  | _ => none

/-- The parts of an array of layout `l` that is a literal (see `JsExpr.arrayLitParts?`). -/
def JsArrayLayout.litParts? {C M : List JsTy} {A E : JsTy} :
    (l : JsArrayLayout A E) → JsExpr C M A → Option (JsParts C M A E)
  | .generic _, a => a.arrayLitParts?
  | .typed _, .array_mk l' qs => some (JsArrayLayout.elem_unique l' (.typed _) ▸ qs)
  | .typed _, _ => none

/-- The spreads of array literals (of the layout `l`) replaced by their elements. -/
def JsParts.flatten {C M : List JsTy} {A E : JsTy} (l : JsArrayLayout A E) :
    JsParts C M A E → JsParts C M A E
  | .nil => .nil
  | .elem e ps => .elem e (ps.flatten l)
  | .spread a ps =>
    match l.litParts? a with
    | some qs => qs.append (ps.flatten l)
    | none => .spread a (ps.flatten l)

/-- The spreads of list literals replaced by their elements. -/
def JsParts.flattenList {C M : List JsTy} {α : JsTy} :
    JsParts C M (.list α) α → JsParts C M (.list α) α
  | .nil => .nil
  | .elem e ps => .elem e ps.flattenList
  | .spread a ps =>
    match a.listLitParts? with
    | some qs => qs.append ps.flattenList
    | none => .spread a ps.flattenList

/-- One step of flattening. -/
def flattenNode {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → JsExpr C M τ
  | .array_mk l ps => .array_mk l (ps.flatten l)
  | .list_mk ps => .list_mk ps.flattenList
  | e => e

/-- The flattening rewrite. -/
def flattenRw : JsExprRewrite := ⟨fun _ _ _ e => flattenNode e⟩

/-- Are all the arguments variables, globals or literals? -/
def JsArgs.allAtoms {C M σs : List JsTy} : JsArgs C M σs → Bool
  | .nil => true
  | .cons a as => a.isAtom && as.allAtoms

/-- A variable, a literal, or an inlined operation that has no effect and cannot fail on
    those (`xs` as an array, `a.length`): an expression that can be evaluated later, or not
    at all, without changing anything. -/
def JsExpr.isCheapPure {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .inlined (e := .pure) (t := .doesntThrow) _ as => as.allAtoms
  | e => e.isAtom

/-- A cheap pure expression (`JsExpr.isCheapPure`), or a spread of one: a part of an array
    literal that has no effect, cannot fail and is cheap. -/
def JsParts.isMovable {C M : List JsTy} {A E : JsTy} : JsParts C M A E → Bool
  | .nil => true
  | .elem e ps => e.isCheapPure && ps.isMovable
  | .spread a ps => a.isCheapPure && ps.isMovable

/-- An array or list literal that can be moved to its use (`[]` written by an inlined
    operation, `Array.emptyWithCapacity n`, too). -/
def JsExpr.isMovableArray {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .array_mk (.generic _) ps => ps.isMovable
  | .list_mk ps => ps.isMovable
  | .inlined (.array__lean_array_mk _) (.cons (.list_mk ps) .nil) => ps.isMovable
  | .inlined (.array__lean_array_to_list _) (.cons (.array_mk (.generic _) ps) .nil) =>
    ps.isMovable
  | .inlined op args => (match op.template with | .emptyArray => true | _ => false) && args.allAtoms
  | _ => false

/-- `const x = [ … ]; rest` with `x` used once in `rest`, not in a loop or a closure, and
    no mutable variable of the literal reassigned in `rest`: `rest` with the literal for
    `x`, flattened. -/
def inlineArrayNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ e rest) =>
    if !e.isMovableArray then b else
    let occs := rest.occs
    let uses := occs.filter (·.is ⟨false, 0⟩)
    let stable := e.occs.all fun o =>
      !o.isMut || !occs.any fun r => r.write && r.is ⟨true, o.idx⟩
    if uses.size == 1 && !uses.any (·.again) && stable then
      (rest.subst (JsSubst.inst e)).mapBU flattenRw .id
    else b
  | b => b

/-- Flatten the array literals, and inline the ones used once (see above). -/
def inlineArrays {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  b.mapBU flattenRw ⟨fun _ _ _ _ b => inlineArrayNode b⟩

end MoreJs

end
