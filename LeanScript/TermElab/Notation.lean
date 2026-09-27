module

public import LeanScript.Term.Build
public import LeanScript.TyElab.Notation
public meta import LeanScript.TermElab.Anf

@[expose] public section

set_option autoImplicit false

/-!
# `[Term| …]`: a direct-style notation for normal-form terms

`[Term| e]` elaborates the surface syntax `e` to a `LeanScript.Term Δ d Φ Γ τ js o` (the
signature, depth, contexts, type, join points and level are left to unification with the
expected type).  When the expected type is a `PExpr` or a `Neu`, it elaborates to one of those
instead.

The surface syntax is in **direct style**: any term can be an operand of any other.  It is
normalised (`LeanScript.TermElab.Anf`, a normaliser by evaluation) into the grammar of normal
forms: a closure or a delay is bound by `letV` (a known value, shared by name), a call, a fold
or a force with an open operand by `letE`, a redex on known values is computed (a closed
closure applied to a closed argument, a case analysis of a constructor, a fold over a literal
with a closed body, a call of an extern on closed arguments), and a branch in the middle of a
computation gets a join point for the rest of it.

The notation follows the datatype closely: variables are **de Bruijn indices** `#i` of the
source (no names are bound or captured; the normaliser sorts them into known values and
unknowns), join points `^i`, binders are written `_`, and the forms without dedicated syntax
are the constructors' own names with the constructors' own argument order.

| surface syntax                           | normal form                                      |
|------------------------------------------|--------------------------------------------------|
| `#i`                                     | the variable bound `i` binders out (`Neu.var` of an unknown, `PExpr.kvar` of a known value, or the value itself) |
| `fun _ (_ : τ) => e`                     | `Term.letV (Val.lam (Body.closed …/Body.opened …))` (`τ` in the `[Ty| …]` syntax) |
| `f a`                                    | `Term.letE (Comp.app f a)` when `f` or `a` is open; the body of `f` with `a` for its parameter when both are closed |
| `let _ := e; b`, `let _ : τ := e; b`     | `b` with `e` in place (a variable, a literal, a known value), `Comp.share` of a compound neutral `e`, `Term.letV` of a data literal |
| `3`, `"s"`, `true`, `false`              | `PExpr.ofNat 3`, `.lit .string "s"`, `.lit .bool true`, … |
| `lit p v`                                | `PExpr.lit p v`                                  |
| `extern ‹e› a b`                         | `Neu.extern e` on the arguments `a`, `b` when one is open, else its value `PExpr.externLit e …` |
| `if c then a else b`                     | `Branch.ite c a b` (with a join point when not in tail position, or `Neu.cond` when both branches are pure); the branch when `c` is known |
| `cond c a b`                             | the pure conditional `Neu.cond c a b`; the branch when `c` is known |
| `nat_rec n z s`                          | `Comp.nat_rec n z s`; unrolled when `n`, `z` and `s` are closed |
| `enum_mk i`                              | `PExpr.enum_mk _ i`                              |
| `match e with \| 0 => a \| 1 => b \| _ => c` | `Branch.enumList` (the last branch is the default) |
| `(a, b, c)`                              | `PExpr.record_mk` of the fields `a`, `b`, `c`    |
| `let (_, _, _) := e; b`                  | `Term.record_casesOn e b`                        |
| `union_mk i a b`                         | `PExpr.union_mk` of constructor `i` (by position) of the arguments `a`, `b` |
| `match e with \| · => a \| _ => b \| (_, _) => c` | `Branch.union_casesOn e` of the branches `a`, `b`, `c` |
| `#[a, b]`                                | `PExpr.array_mk` of the elements                 |
| `array_foldl arr init s`                 | `Comp.array_foldl arr init s`; unrolled over a literal when all is closed |
| `data_in b j e`, `data_out b j e`        | `PExpr.data_in b j e`, `Neu.data_out b j e` (`e` itself for `data_out b j (data_in b j e)`) |
| `data_rec b ρ br₀ … brₖ j e`             | `Comp.data_rec b ρ _ brs j e`, branch `i` of `brs` is `brᵢ` |
| `data_brec b ρ k br₀ … brₖ j e`          | `Comp.data_brec b ρ k _ brs j e`                 |
| `thunk_mk e`, `thunk_force e`            | `Val.thunk_mk e`, `Comp.thunk_force e` (a `Thunk τ`) |
| `lazy_mk e`, `lazy_force e`              | `Val.lazy_mk e`, `Comp.lazy_force e` (a `Unit → τ`) |
| `join _ (_ : τ) := b; m`                 | `Branch.join τ _ _ b m`, in front of the next branch of `m` (`b` inlined where `m` jumps to it in straight-line code): `b` sees the parameter as `#0`, `m` the join point as `^0` |
| `jump ^j e`                              | `Term.jump j e`                                  |
| `(e : τ)`                                | `e`, at the type `τ` (in the `[Ty| …]` syntax)   |
| `‹t›`                                    | the closed Lean term `t : PExpr …`, generic in its contexts |
| `‹f›(a, b)`                              | the Lean term `f a b`: a Lean function of pure expressions whose level is the smallest of its arguments' (a constructor function) |

**Variables and binders.**  A variable is only ever `#i`, the de Bruijn index of the
source (`0` is the innermost binder); an identifier is never a variable, and never a Lean
term either: every Lean term, even a single name, is written `‹t›`.  The binders follow the
constructors: in `nat_rec n z s` the step `s` sees the answer as `#0` and the predecessor as
`#1`; in `array_foldl arr init s` it sees the element as `#0` and the accumulator as `#1`;
`let (_, _) := e; b` and the patterns of a union see the fields with the first field innermost
(`#0`); a branch of `data_rec`/`data_brec` sees the member's body as `#0`.  A variable past the
binders of the source is an unknown of the enclosing context (`Γ` of the expected type).

**Lean arguments.**  In `lit`, `extern`, `enum_mk`, `union_mk`, `data_in`, `data_out`,
`data_rec` and `data_brec` the leaf, value, extern, constructor number, block, member, answer
types and depth are Lean terms: a number, a string or `‹t›`.

**Usages.**  Every binder is annotated `many` (sound; `Term.dce` makes the annotations exact).

A numeral takes its leaf type from the expected type (`PExpr.ofNat`), so its type must be
known from the context.
-/

namespace LeanScript

/-! ## Syntax -/

/-- The surface syntax of a term (`[Term| …]`). -/
declare_syntax_cat lsterm
/-- A binder of `fun` and `join`: `_`, or `(_ : τ)`. -/
declare_syntax_cat lsbinder
/-- A placeholder for a bound variable: `_`. -/
declare_syntax_cat lshole
/-- A pattern of `match`. -/
declare_syntax_cat lspat

/-- A variable, by de Bruijn index. -/
syntax:max (name := lstermBVar) "#" noWs num : lsterm
/-- A join point, by de Bruijn index (only as the first argument of `jump`). -/
syntax:max (name := lstermJVar) "^" noWs num : lsterm
/-- A constructor name (`nat_rec`, …), or `true`/`false`. -/
syntax:max ident : lsterm
/-- A literal. -/
syntax:max num : lsterm
/-- A literal. -/
syntax:max str : lsterm
/-- A closed Lean term of type `PExpr`, generic in its contexts. -/
syntax:max (name := lstermEmbed) "‹" term "›" : lsterm
/-- A Lean function of pure expressions, applied: `‹f›(a, b)` is `f a b`. -/
syntax:max "‹" term "›" noWs "(" lsterm,* ")" : lsterm
syntax:max "(" lsterm ")" : lsterm
/-- A type ascription. -/
syntax:max "(" lsterm " : " lsty ")" : lsterm
/-- A record. -/
syntax:max (name := lstermTuple) "(" lsterm ", " lsterm,+ ")" : lsterm
/-- An array. -/
syntax:max "#[" lsterm,* "]" : lsterm
/-- Application. -/
syntax:100 (name := lstermApp) lsterm:100 ppSpace lsterm:101 : lsterm

syntax "_" : lshole

syntax "_" : lsbinder
syntax "(" "_" " : " lsty ")" : lsbinder

syntax (name := lstermFun) "fun" (ppSpace lsbinder)+ " => " lsterm : lsterm
syntax (name := lstermLet) "let " "_" (" : " lsty)? " := " lsterm "; " lsterm : lsterm
syntax (name := lstermLetTuple) "let " "(" lshole ", " lshole,+ ")" " := " lsterm "; " lsterm : lsterm
syntax (name := lstermIf) "if " lsterm " then " lsterm " else " lsterm : lsterm
/-- `join _ x := body; main`: a join point (the first `_`), whose parameter is `x`. -/
syntax (name := lstermJoin) "join " "_ " lsbinder " := " lsterm "; " lsterm : lsterm

syntax "·" : lspat
syntax "_" : lspat
syntax "(" lshole ", " lshole,+ ")" : lspat
syntax num : lspat
syntax (name := lstermMatch) "match " lsterm " with" (ppDedent(ppLine) " | " lspat " => " lsterm)+ : lsterm

/-- `[Term| e]`: the term written in the surface syntax `e` (see the module doc). -/
syntax:max (name := lstermQuote) "[Term| " lsterm "]" : term

end LeanScript

meta section

namespace LeanScript.Notation

open Lean Meta Elab Term
open LeanScript.Anf (Src)

/-! ## Elaboration: surface syntax → source tree → normal form -/

/-- The constructors written as an application of their name. -/
def specialForms : List Name :=
  [`lit, `extern, `cond, `nat_rec, `enum_mk, `union_mk, `array_foldl, `data_in, `data_out, `data_rec,
   `data_brec, `thunk_mk, `thunk_force, `lazy_mk, `lazy_force, `jump]

/-- The head and the arguments of an application. -/
partial def appSpine (e : TSyntax `lsterm) (args : List (TSyntax `lsterm) := []) :
    TSyntax `lsterm × List (TSyntax `lsterm) :=
  match e with
  | `(lsterm| $f $a) => appSpine f (a :: args)
  | _ => (e, args)

/-- A Lean term given as an argument of a constructor: a number, a string or `‹t›`. -/
partial def leanArg : TSyntax `lsterm → TermElabM Lean.Term
  | `(lsterm| $n:num) => pure n
  | `(lsterm| $s:str) => pure s
  | `(lsterm| ‹$t›) => pure t
  | `(lsterm| ($t)) => leanArg t
  | t => throwErrorAt t "expected a Lean term here: a number, a string or `‹term›`"

/-- The components of a record literal `(a, b, …)`, or `none`. -/
def tupleElems? (e : TSyntax `lsterm) : Option (List (TSyntax `lsterm)) :=
  if e.raw.isOfKind ``LeanScript.lstermTuple then
    some (e.raw[1] :: e.raw[3].getSepArgs.toList |>.map (⟨·⟩))
  else none

/-- The number of variables a pattern of a union binds. -/
def patBinds (p : TSyntax `lspat) : TermElabM Nat :=
  match p with
  | `(lspat| ·) => pure 0
  | `(lspat| _) => pure 1
  | `(lspat| ($_, $hs,*)) => pure (hs.getElems.size + 1)
  | _ => throwErrorAt p "expected `·`, `_` or `(_, _, …)`"

mutual

/-- The source tree of a surface term. -/
partial def toSrc : TSyntax `lsterm → TermElabM Src
  | `(lsterm| #$n:num) => pure (.var n.getNat)
  | `(lsterm| ^$n:num) => throwErrorAt n "a join point `^i` is only the first argument of `jump`"
  | `(lsterm| $n:num) => do return .lit (← `(LeanScript.PExpr.ofNat $n)) (.nat n.getNat)
  | `(lsterm| $s:str) => do
      return .lit (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.string $s)) .other
  | `(lsterm| ‹$t›) => pure (.embed t)
  | `(lsterm| ‹$f›($as,*)) => do return .ctor f (← as.getElems.mapM toSrc) none
  | `(lsterm| ($e)) => toSrc e
  | `(lsterm| ($e : $τ)) => do return .ascribe (← toSrc e) (← `([Ty| $τ]))
  | `(lsterm| #[$es,*]) => do return .array (← es.getElems.mapM toSrc)
  | `(lsterm| fun $bs* => $b) => funSrc bs.toList b
  | `(lsterm| let _ := $e; $b) => do return .letE (← toSrc e) (← toSrc b)
  | `(lsterm| let _ : $τ := $e; $b) => do
      return .letE (.ascribe (← toSrc e) (← `([Ty| $τ]))) (← toSrc b)
  | `(lsterm| let ($_, $hs,*) := $e; $b) => do
      return .recordCases (← toSrc e) (hs.getElems.size + 1) (← toSrc b)
  | `(lsterm| if $c then $a else $b) => do return .ite none (← toSrc c) (← toSrc a) (← toSrc b)
  | `(lsterm| join _ $x := $body; $main) => do
      let ty? ← match x with
        | `(lsbinder| (_ : $τ)) => some <$> `([Ty| $τ])
        | _ => pure none
      return .join ty? (← toSrc body) (← toSrc main)
  | `(lsterm| match $e with $[| $ps => $bs]*) => matchSrc e ps.toList bs.toList
  | `(lsterm| $id:ident) =>
      match id.getId.eraseMacroScopes with
      | `true => return Src.boolLit true
      | `false => return Src.boolLit false
      | _ => specialSrc id []
  | e@`(lsterm| $_ $_) => do
      match tupleElems? e with
      | some _ => tupleSrc e
      | none =>
      let (f, args) := appSpine e
      if let `(lsterm| $id:ident) := f then
        if specialForms.contains id.getId.eraseMacroScopes then
          return ← specialSrc id args
      let mut r ← toSrc f
      for a in args do
        r := .app r (← toSrc a)
      return r
  | e => if (tupleElems? e).isSome then tupleSrc e
      else throwErrorAt e "unsupported term syntax"

/-- A record literal. -/
partial def tupleSrc (e : TSyntax `lsterm) : TermElabM Src := do
  let some es := tupleElems? e | throwErrorAt e "expected a record"
  return .record (← es.toArray.mapM toSrc)

/-- `fun _ … _ => b`. -/
partial def funSrc : List (TSyntax `lsbinder) → TSyntax `lsterm → TermElabM Src
  | [], b => toSrc b
  | x :: xs, b => do
      match x with
      | `(lsbinder| (_ : $τ)) => return .lam (some (← `([Ty| $τ]))) (← funSrc xs b)
      | `(lsbinder| _) => return .lam none (← funSrc xs b)
      | _ => throwErrorAt x "unsupported binder"

/-- `match e with | p => b …`: an enum when the patterns are numbers, a union otherwise. -/
partial def matchSrc (e : TSyntax `lsterm) (ps : List (TSyntax `lspat))
    (bs : List (TSyntax `lsterm)) : TermElabM Src := do
  let e' ← toSrc e
  let isEnum := ps.any fun | `(lspat| $_:num) => true | _ => false
  if isEnum then
    let n := ps.length
    let pats ← ps.toArray.mapIdxM fun i p => do
      match p with
      | `(lspat| $k:num) => pure (some k.getNat)
      | `(lspat| _) =>
          if i + 1 == n then pure none
          else throwErrorAt p "only the last branch may be `_`"
      | _ => throwErrorAt p "expected a constructor number"
    return .enumCases none e' pats (← bs.toArray.mapM toSrc)
  else
    if ps.length < 2 then throwErrorAt e "a union has at least two constructors"
    let brs ← (ps.zip bs).toArray.mapM fun (p, b) => return (← patBinds p, ← toSrc b)
    return .unionCases none e' brs

/-- A constructor, applied to `args`. -/
partial def specialSrc (id : Ident) (args : List (TSyntax `lsterm)) : TermElabM Src := do
  let f := id.getId.eraseMacroScopes
  let bad {α : Type} (usage : String) : TermElabM α :=
    throwErrorAt id s!"`{f}` is used as `{usage}`"
  match f, args with
  | `lit, [p, v] => do
      let val : Anf.LitVal := match v with
        | `(lsterm| $k:num) => .nat k.getNat
        | _ => .other
      return .lit (← `(LeanScript.PExpr.lit $(← leanArg p) $(← leanArg v))) val
  | `lit, _ => bad "lit p v"
  | `extern, e :: as => do return .extern (← leanArg e) (← as.toArray.mapM toSrc)
  | `extern, _ => bad "extern ‹e› a₁ … aₙ"
  | `cond, [c, a, b] => do return .cond (← toSrc c) (← toSrc a) (← toSrc b)
  | `cond, _ => bad "cond c a b"
  | `nat_rec, [n, z, s] => do return .natRec none (← toSrc n) (← toSrc z) (← toSrc s)
  | `nat_rec, _ => bad "nat_rec n z s"
  | `enum_mk, [i] => do
      let stx ← `(LeanScript.PExpr.enum_mk _ $(← leanArg i))
      match i with
      | `(lsterm| $k:num) => return .enumMk (some k.getNat) stx
      | _ => return .enumMk none stx
  | `enum_mk, _ => bad "enum_mk i"
  | `union_mk, i :: as => do
      let pos? := match i with
        | `(lsterm| $k:num) => some k.getNat
        | _ => none
      let ix ← `(LeanScript.Ctors.ix _ $(← leanArg i) (by decide))
      return .union pos? ix (← as.toArray.mapM toSrc)
  | `union_mk, _ => bad "union_mk i a₁ … aₙ"
  | `array_foldl, [arr, init, s] => do
      return .arrayFoldl (← toSrc arr) (← toSrc init) (← toSrc s)
  | `array_foldl, _ => bad "array_foldl arr init s"
  | `data_in, [b, j, e] => do return .dataIn (← leanArg b) (← leanArg j) (← toSrc e)
  | `data_in, _ => bad "data_in b j e"
  | `data_out, [b, j, e] => do return .dataOut (← leanArg b) (← leanArg j) (← toSrc e)
  | `data_out, _ => bad "data_out b j e"
  | `data_rec, b :: ρ :: rest@(_ :: _ :: _ :: _) => do
      let brs ← (rest.take (rest.length - 2)).toArray.mapM toSrc
      return .dataRec none (← leanArg b) (← leanArg ρ) none brs
        (← leanArg rest[rest.length - 2]!) (← toSrc rest[rest.length - 1]!)
  | `data_rec, _ => bad "data_rec b ρ br₀ … brₖ j e"
  | `data_brec, b :: ρ :: k :: rest@(_ :: _ :: _ :: _) => do
      let brs ← (rest.take (rest.length - 2)).toArray.mapM toSrc
      return .dataRec none (← leanArg b) (← leanArg ρ) (some (← leanArg k)) brs
        (← leanArg rest[rest.length - 2]!) (← toSrc rest[rest.length - 1]!)
  | `data_brec, _ => bad "data_brec b ρ k br₀ … brₖ j e"
  | `thunk_mk, [e] => do return .delayMk false none (← toSrc e)
  | `thunk_mk, _ => bad "thunk_mk e"
  | `thunk_force, [e] => do return .force false none (← toSrc e)
  | `thunk_force, _ => bad "thunk_force e"
  | `lazy_mk, [e] => do return .delayMk true none (← toSrc e)
  | `lazy_mk, _ => bad "lazy_mk e"
  | `lazy_force, [e] => do return .force true none (← toSrc e)
  | `lazy_force, _ => bad "lazy_force e"
  | `jump, [j, e] =>
      match j with
      | `(lsterm| ^$n:num) => do return .jump n.getNat (← toSrc e)
      | _ => bad "jump ^j e"
  | `jump, _ => bad "jump ^j e"
  | _, _ => throwErrorAt id s!"unknown constructor `{f}`: a variable is written `#i` \
      and a Lean term `‹{f}›`"

end

/-- `[Term| e]`: normalised to a pure expression, a neutral expression or a statement,
    following the expected type (a statement when it is not known). -/
@[term_elab lstermQuote]
def elabTermQuote : TermElab := fun stx expected? => do
  -- the layer is chosen by the expected type: wait for it when it is not known yet
  tryPostponeIfNoneOrMVar expected?
  let s ← toSrc ⟨stx[1]⟩
  let layer ← match expected? with
    | some t => pure (← whnfR (← instantiateMVars t)).getAppFn.constName?
    | none => pure none
  let out ← match layer with
    | some ``LeanScript.PExpr => s.toPExpr
    | some ``LeanScript.Neu => s.toNeu
    | _ => s.toTerm
  withRef stx <| elabTerm out expected?

end LeanScript.Notation

end
