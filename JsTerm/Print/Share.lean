import JsTerm.Print.Mini
import JsTerm.Lower.Tail
import JsTerm.Lower.Unroll
import JsTerm.Lower.AddChain
import JsTerm.Lower.Sink
import JsTerm.Lower.MergeIte
import JsTerm.Lower.ShareTail

set_option autoImplicit false

/-!
# Functions sharing one worker

The functions of a `mutual` group recursing on a `Nat` (`testEven`/`testOdd`) are each
translated into the same loop over all the group, which differ only in the tag of the function
the loop starts with: the literal initial value of their first mutable variable (`let p$1 =
true;` / `let p$1 = false;`).  Such functions are written once, as a worker private to the
module taking that value as its first parameter, and each of them as a call of the worker:

```js
const testEven$shared = (tag, n, b) => { let p$1 = tag; … };
export const testEven = (n, b) => testEven$shared(true, n, b);
export const testOdd = (n, b) => testEven$shared(false, n, b);
```

A `mutual` pair whose loop can do without the tag is not shared that way but rewritten
first (`pairTagLoops`, `JsTerm.Lower.Unroll`): the first function's loop runs two iterations
per step, and the second function runs one iteration and calls the first.

Two functions share a worker only when the JavaScript of their two workers is the same text,
so the rewrite never changes what a function computes: each calls a function whose code is
its own, with its own first value as a parameter.

(Not a `module`: it prints with `LanguageJavascriptMini`, which is not written in the module
system.)
-/

namespace MoreJs

open Language.JavaScript Language.JavaScript.MiniAST

theorem pushAll_append_one {α : Type} (us c : List α) (t : α) :
    pushAll us c ++ [t] = pushAll us (c ++ [t]) := by
  induction us generalizing c with
  | nil => rfl
  | cons u us ih => exact ih (u :: c)

/-- The shape of a literal. -/
def JsExpr.litShape? {S : JsSig} {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option JsLitShape
  | .lit l => some l.shape
  | _ => none

/-- The renaming of `C` into `pushAll us C`. -/
def wkPushAll {C : List JsTy} : (us : List JsTy) → JsRenM Id C (pushAll us C)
  | [] => fun x => x
  | _ :: us => fun x => wkPushAll us (JsMem.succ x)

/-- The renaming of `C` into `C ++ [τ]` (a constant below all the others). -/
def wkBottom {C : List JsTy} (τ : JsTy) : JsRenM Id C (C ++ [τ]) := fun x => x.appendR [τ]

/-- The type of the first mutable variable of a block, when the block starts with constants
    and patterns, then `let x = lit;`. -/
partial def JsBlock.firstLitTy? {S : JsSig} {C M J : List JsTy} {k : JsEnd} :
    JsBlock S C M J k → Option JsTy
  | .letMut (τ := σ) _ e _ => e.litShape?.map fun _ => σ
  | .const _ _ rest => rest.firstLitTy?
  | .destructure _ _ rest => rest.firstLitTy?
  | _ => none

/-- A block that starts with constants and patterns, then `let x = lit;` (`lit` of type `τ`),
    over one more constant `tag` below all the others, starting with `let x = tag;` instead;
    and the literal. -/
partial def JsBlock.abstractLit {S : JsSig} {C M J : List JsTy} {k : JsEnd} (τ : JsTy)
    (tag : JsMem (C ++ [τ]) τ) : JsBlock S C M J k → Option (JsBlock S (C ++ [τ]) M J k × JsLitShape)
  | .letMut (τ := σ) x e rest => do
    let lit ← e.litShape?
    if h : τ = σ then
      let rest' := Id.run (rest.renameM (wkBottom τ) JsRen.id)
      some (.letMut x (h ▸ JsExpr.cvar tag) rest', lit)
    else none
  | .const x e rest => do
    let e' := Id.run (e.renameM (wkBottom τ) JsRen.id)
    let (r, lit) ← rest.abstractLit τ tag.succ
    some (.const x e' r, lit)
  | .destructure (us := us) e sel rest => do
    let e' := Id.run (e.renameM (wkBottom τ) JsRen.id)
    have heq : pushAll us C ++ [τ] = pushAll us (C ++ [τ]) := pushAll_append_one us C τ
    let tag' : JsMem (pushAll us C ++ [τ]) τ := heq ▸ Id.run (wkPushAll us tag)
    let (r, lit) ← rest.abstractLit τ tag'
    some (.destructure e' sel (heq ▸ r), lit)
  | _ => none

/-- The worker `name` of a function whose body starts (after constants and patterns) with
    `let x = lit;`: the function of one more parameter `tag`, first, whose body starts with
    `let x = tag;` instead; and the literal. -/
def JsFun.worker? (f : JsFun) (name : String) : Option (JsFun × JsLitShape) := do
  if f.params.isEmpty then none
  let τ ← f.body.firstLitTy?
  let ps := f.params.map (·.2)
  have heq : pushAll ps [] ++ [τ] = pushAll ps [τ] := pushAll_append_one ps [] τ
  let tag ← JsMem.ofIndex? (pushAll ps [] ++ [τ]) ps.length τ
  let (b, lit) ← f.body.abstractLit τ tag
  let body : JsBlock f.sig (pushAll (τ :: ps) []) [] [] (.ret f.ret) := heq ▸ b
  let paramNames := f.params.map (·.1)
  let tagName := (List.range (paramNames.length + 1)).map
      (fun i => if i == 0 then "tag" else s!"tag{i}")
    |>.find? (!paramNames.contains ·) |>.getD "tag"
  return ({ name, leanName := f.leanName, sig := f.sig, params := (tagName, τ) :: f.params,
            ret := f.ret, body, exported := false,
            notes := f.notes }, lit)

/-- The text of a function. -/
def JsFun.text (f : JsFun) : String := printProgram ⟨[f.toMini]⟩

/-- The functions `funs`, the pairs of them that compute the same loop over a `Bool` tag up to
    the initial value of the tag (the `mutual` pairs recursing on a `Nat`, `testEven`/`testOdd`)
    rewritten without the tag (`JsTerm.Lower.Unroll`): the first one with its loop unrolled (two
    iterations per step, so that the tag is always the same at the start of a step), the second
    one as one iteration of its own state followed by a call of the first one (or, when its
    arguments cannot be rebuilt, with its own loop unrolled too). -/
def pairTagLoops (funs : List JsFun) : List JsFun := Id.run do
  let arr := funs.toArray
  let keyOf (f : JsFun) : Option (String × Bool) :=
    match f.worker? "w" with
    | some (w, .bool c) =>
      if (w.params.headD ("", .terminal .bool)).2 == .terminal .bool then some (w.text, c) else none
    | _ => none
  let keys := arr.map keyOf
  let mut out := arr
  let mut done : Array Bool := arr.map fun _ => false
  for i in [0:arr.size] do
    if done[i]! then continue
    let some f := arr[i]? | continue
    let some (key, cf) := keys[i]?.join | continue
    let js := (List.range arr.size).filter fun j => j > i && !done[j]! &&
      (match arr[j]?, keys[j]?.join with
       | some g, some (k, _) => g.params == f.params && g.ret == f.ret && k == key
       | _, _ => false)
    let [j] := js | continue
    let some g := arr[j]? | continue
    let some (_, cg) := keys[j]?.join | continue
    if cg == cf then continue
    let some f' := f.unrollTag? | continue
    let some g' := (g.peelInto? f cg cf).orElse fun _ => g.unrollTag? | continue
    out := (out.set! i f').set! j g'
    done := (done.set! i true).set! j true
  return out.toList

/-- The length of the JavaScript of a block, printed on its own (its variables all named `v`,
    its join points all `L`): the measure of `JsBlock.shareTails`. -/
def blockCost (S : JsSig) : BlockCost S := fun {C M J _} b =>
  let sc : Scope := { c := C.map fun _ => ident "v", m := M.map fun _ => "v",
                      joins := J.map fun _ => ("L", "v") }
  let ss := (blockToMini sc {} b).run' {}
  (printProgram ⟨ss.map .stmt⟩).length

/-- `blockCost` of the block with its tests that end in the same statements merged (as it is
    printed in the end). -/
def mergedCost (S : JsSig) : BlockCost S := fun b => blockCost S b.mergeIte

/-- The functions `funs`, those that compute the same up to the literal initial value of their
    first mutable variable written as calls of one shared worker (put just before the first of
    them); first, the pairs of `pairTagLoops` without their tag, then the additions of
    literals folded through constants (`JsTerm.Lower.AddChain`), the constants read on one
    path only computed on it (`JsTerm.Lower.Sink`), the tests that end in the same statements
    merged (`JsTerm.Lower.MergeIte`), and the tails that several branches of a test end in
    written once after a labelled block (`JsTerm.Lower.ShareTail`, where that makes the
    JavaScript shorter, the tests then merged again). -/
def shareWorkers (funs : List JsFun) : List JsFun := Id.run do
  let funs := (pairTagLoops funs).map fun f => (f.foldAdds.sink.mergeIte.shareTails mergedCost).mergeIte
  let arr := funs.toArray.map fun _ => ()
  let names := funs.map (·.name)
  -- for each function: the worker put before it, and the call it is written as
  let mut before : Array (Option JsFun) := arr.map fun _ => none
  let mut delegate : Array (Option (String × JsLitShape)) := arr.map fun _ => none
  for (f, i) in funs.zipIdx do
    if (delegate[i]!).isSome then continue
    let wname := (List.range 100).map (fun k => if k == 0 then s!"{f.name}$shared"
      else s!"{f.name}$shared{k}") |>.find? (!names.contains ·) |>.getD s!"{f.name}$shared"
    let some (wf, lf) := f.worker? wname | continue
    let key := wf.text
    let mut sharers : Array String := #[]
    for (g, j) in funs.zipIdx do
      if j ≤ i || (delegate[j]!).isSome then continue
      unless g.params == f.params && g.ret == f.ret do continue
      match g.worker? wname with
      | some (wg, lg) =>
        if wg.text == key then
          delegate := delegate.set! j (some (wname, lg))
          sharers := sharers.push g.name
      | none => pure ()
    unless sharers.isEmpty do
      let all := ", ".intercalate ((f.name :: sharers.toList).map (s!"`{·}`"))
      let tagName := (wf.params.headD ("tag", .terminal .bool)).1
      before := before.set! i (some { wf with notes := wf.notes ++
        [s!"(private) the code of {all}, which call it with the initial value of its first \
          variable as `{tagName}`"] })
      delegate := delegate.set! i (some (wname, lf))
  let mut out : Array JsFun := #[]
  for (f, i) in funs.zipIdx do
    if let some w := before[i]! then out := out.push w
    out := out.push { f with delegate? := delegate[i]! }
  return out.toList

end MoreJs
