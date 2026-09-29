module

public import JsTerm.Passes.Contify

@[expose] public section

set_option autoImplicit false

/-!
# Emitting clean JavaScript: the rules the generator applies to each statement

The conversion from `Term` (`JsTerm.Lower.FromTerm`) never builds a statement of the
JavaScript grammar with a bare constructor: it **emits** it (`JsBlock.emit`), and emitting a
statement puts it in normal form for the rules of the backend, the parts of the statement being
in normal form already (they were emitted before it).  So the function the conversion answers
is in normal form when it is built, and there is no pass over it afterwards.

The rules are the lowering clean-ups, the imperative rewrites and the target-specific
simplifications that cannot be written on `Term` (they need `let`, assignments, loops, or the
JavaScript representation of the values), each one written for one statement whose parts are
clean (the files of `JsTerm/Passes`):

* on expressions (`emitExprRules`): a closure called on the spot is its body (`betaNode`), the
  spreads of array literals are flattened (`flattenNode`);
* on statements (`emitBlockRules`): copy propagation and the known patterns (`cleanupNode`),
  `const x = e; return x;` (`peepholeNode`), array literals used once (`inlineArrayNode`), and
  the rules of `tidyStep`: constants used once right away, local functions as join points,
  unboxed accumulators, flattened join points, copies of mutable variables, dead constants,
  assignments moved up, loops of tail calls.

When a rule rewrites a statement, the rewritten statement is emitted again, wholly
(`JsBlock.normalize`): a rule that substitutes a value into the rest of a block (copy
propagation, a constant used once) can make a rule fire there.

A few rules are only valid when no closure of the function reads a mutable variable
(`noCapture`, see `tidyStep`); the conversion decides it for the whole function before it
emits anything (`EmitCfg`).

Emitting the statements as they are built gives the code the former pipeline of passes over the
finished function gave (the former `cleanup`, `peephole`, `inlineArrays`, `peephole`, `cleanup`,
`peephole`, then `tidy` until nothing changed; those drivers are gone): the snapshots are
unchanged.
-/

namespace MoreJs

/-- What the emitter of one function needs to know. -/
structure EmitCfg where
  /-- Apply the rules at all (off for the first run of the conversion of a function, which only
      finds out whether a closure reads a mutable variable). -/
  rules : Bool := true
  /-- No closure of the function reads a mutable variable (see `tidyStep`). -/
  noCapture : Bool := true
  deriving Inhabited

/-- The rules on one expression whose parts are clean. -/
def emitExprRules : JsExprRewrite := ⟨fun _ _ _ e => betaNode (flattenNode e)⟩

/-- The rules on one statement whose parts are clean. -/
def emitBlockRules (noCapture : Bool) : JsBlockRewrite := ⟨fun _ _ _ _ b =>
  peepholeNode (cleanupNode (tidyStep noCapture (inlineArrayNode (peepholeNode (cleanupNode b)))))⟩

/-- A statement with the rules applied everywhere in it, again and again until nothing changes
    (at most `fuel` rounds). -/
def JsBlock.normalize (noCapture : Bool) {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k)
    (fuel : Nat := 16) : JsBlock C M J k :=
  go fuel b (b.pretty "")
where
  /-- The rounds. -/
  go : Nat → JsBlock C M J k → String → JsBlock C M J k
    | 0, b, _ => b
    | n + 1, b, s =>
      let b' := b.mapBU emitExprRules (emitBlockRules noCapture)
      let s' := b'.pretty ""
      if s' == s then b' else go n b' s'

/-- The expressions of the statement itself (not of the statements it is followed by or
    contains), rewritten by `f`. -/
def JsBlock.mapOwnExprs (f : {C M : List JsTy} → {τ : JsTy} → JsExpr C M τ → JsExpr C M τ)
    {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | .ret e => .ret (f e)
  | .next => .next
  | .jump j e => .jump j (f e)
  | .throw msg => .throw msg
  | .const x e rest => .const x (f e) rest
  | .letMut x e rest => .letMut x (f e) rest
  | .assign x e rest => .assign x (f e) rest
  | .destructure e sel rest => .destructure (f e) sel rest
  | .ite c t e => .ite (f c) t e
  | .enumCases e arms => .enumCases (f e) arms
  | .unionCases e arms => .unionCases (f e) arms
  | .join x b rest => .join x b rest
  | .forRange x nt n b rest => .forRange x nt (f n) b rest
  | .lastIter x nt n b rest => .lastIter x nt (f n) b rest
  | .forOf x l xs b rest => .forOf x l (f xs) b rest

/-- Emit a statement just built, whose statements (the rest, the arms, the bodies) are clean:
    its expressions and itself with the rules applied, and, when that changed it, the whole
    statement again until nothing changes (`JsBlock.normalize`). -/
def JsBlock.emit (ec : EmitCfg) {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) :
    JsBlock C M J k :=
  if !ec.rules then b else
  let b₁ := b.mapOwnExprs (·.mapBU emitExprRules (emitBlockRules ec.noCapture))
  let b₂ := (emitBlockRules ec.noCapture).run _ _ _ _ b₁
  let s := b.pretty ""
  if b₂.pretty "" == s then b else b₂.normalize ec.noCapture

/-- Emit a statement that was rewritten as a whole (a loop body whose `return`s became
    assignments, a block whose `return`s became jumps): the rules everywhere in it, until
    nothing changes. -/
def JsBlock.emitAll (ec : EmitCfg) {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) :
    JsBlock C M J k :=
  if !ec.rules then b else b.normalize ec.noCapture

end MoreJs

end
