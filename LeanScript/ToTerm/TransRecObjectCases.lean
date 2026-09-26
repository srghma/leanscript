module

public meta import LeanScript.ToTerm.TransRecObjectPieces

@[expose] public section

meta section

/-!
# The translation of a recursion on a recursive record: the levels of the fold

`recObjLevel`, `recObjPayload` and their helpers, which build the body of the fold
`LeanScript.ToTerm.transRecObjectBrecOn?` emits, one level of the record at a time.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The two fields of an answer tree `R` of the fold of `info`: the language type of the
    answers, and that of the window below. -/
def recObjTreeFields (info : RecObjInfo) (R : Expr) : MetaM (Expr × Expr) := do
  let .record fsT ← tyView R
    | throwError "`#leanscript_to_term`: internal: an answer tree of {info.ind} is not a record"
  let tTys := (← recordFieldTys fsT).toArray
  unless tTys.size == 2 do
    throwError "`#leanscript_to_term`: internal: an answer tree of {info.ind} has \
      {tTys.size} fields"
  return (tTys[0]!, tTys[1]!)

/-- The de Bruijn variable (`Γ ∋ τ`) of the variable `f` of the context: the argument of the
    `Term.var` that reads it. -/
def TCtx.varIdx (c : TCtx) (f : FVarId) : MetaM Expr :=
  return (← c.var f).appArg!

mutual

/-- Take apart a **window** — the record of fields of one level, with each subvalue
    replaced by its answer tree of depth `j` — bound in `c` as `wv` of type `wTy`, and
    continue with the Lean values of the fields. -/
partial def recObjLevel (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (wv : FVarId) (wTy : Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr)
    (outer : Option (Array Expr) := none) :
    MetaM Expr := do
  if info.isAlias then
    -- a newtype has one field, its body, and the window is that body itself
    return ← recObjPayloadFrom info c answers frontier info.fields #[mkFVar wv] #[wTy] j 0
      #[] k
  let .record fsW ← tyView wTy
    | throwError "`#leanscript_to_term`: internal: the window of the fold is not a record"
  let fTys := (← recordFieldTys fsW).toArray
  unless fTys.size == info.fields.size do
    throwError "`#leanscript_to_term`: internal: the window has {fTys.size} fields, the \
      record {info.ind} {info.fields.size}"
  -- at the top level, a field that does not mention the record is read where the
  -- branch binds it, not out of the window, which holds the same value
  let override : Array (Option Expr) := match outer with
    | some o => info.fields.mapIdx fun i f => match f, o[i]? with
        | .plain _, some v => some v
        | _, _ => none
    | none => #[]
  let body ← recObjPayload info c answers frontier info.fields fTys j k override
  -- `recObjPayload` bound the fields in the context of the branch of this dispatch
  return mkAppN (mkConst `LeanScript.Term.record_casesOn')
    #[c.sg, c.gamma, info.τ, fsW, ← c.var wv, body]

/-- The fields of one constructor of a union field: those that do not mention the record
    are Lean variables; each one that is the record is, in the window, its answer tree —
    at depth `0` the answer alone, which leaves the subvalue a frontier variable, and
    otherwise the answer beside the window of its own fields, which is taken apart in
    turn. -/
partial def recObjPayload (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (pfs : Array RecObjPayloadField) (pTys : Array Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr)
    (override : Array (Option Expr) := #[]) :
    MetaM Expr := do
  unless pfs.size == pTys.size do
    throwError "`#leanscript_to_term`: internal: a constructor of a field of {info.ind} \
      has {pfs.size} fields, its tree {pTys.size}"
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    pfs.mapIdx fun i f => match f with
      | .plain t => (Name.mkSimple s!"p{i}", fun _ => pure t)
      | .self =>
          if j == 0 then (Name.mkSimple s!"ans{i}", fun _ => pure info.τLean)
          else (Name.mkSimple s!"tree{i}", fun _ => pure (mkConst ``Unit))
      | .struct .. => (Name.mkSimple s!"s{i}", fun _ => pure (mkConst ``Unit))
      | .union .. => (Name.mkSimple s!"u{i}", fun _ => pure (mkConst ``Unit))
      | .array .. => (Name.mkSimple s!"a{i}", fun _ => pure (mkConst ``Unit))
      | .fn _ dom =>
          if j == 0 then (Name.mkSimple s!"ans{i}", fun _ => mkArrow dom info.τLean)
          else (Name.mkSimple s!"f{i}", fun _ => pure (mkConst ``Unit))
      | .thunk _ =>
          if j == 0 then (Name.mkSimple s!"ans{i}", fun _ => mkAppM ``Thunk #[info.τLean])
          else (Name.mkSimple s!"t{i}", fun _ => pure (mkConst ``Unit))
  withLocalDeclsD decls fun ps => do
    let c' := c.pushFields (ps.zip pTys |>.map fun (x, t) => (x.fvarId!, t))
    -- a value given from outside replaces the variable, where there is one
    let ps' := ps.mapIdx fun i x => (override[i]?.bind id).getD x
    recObjPayloadFrom info c' answers frontier pfs ps' pTys j 0 #[] k

/-- The fields of one constructor of a union field, from the `i`-th on. -/
partial def recObjPayloadFrom (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (pfs : Array RecObjPayloadField) (ps pTys : Array Expr) (j : Nat)
    (i : Nat) (pvals : Array Expr)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  let go := recObjPayloadFrom info
  if h : i < ps.size then
    match pfs[i]! with
    | .plain _ => go c answers frontier pfs ps pTys j (i + 1) (pvals.push ps[i]) k
    | .struct sc slvls sparams sfs =>
        -- a structure around the record: its case analysis, and its fields read in turn
        let .record fsS ← tyView pTys[i]!
          | throwError "`#leanscript_to_term`: internal: the tree of a structure inside \
              {info.ind} is not a record"
        let sTys := (← recordFieldTys fsS).toArray
        let inner ← recObjPayload info c answers frontier sfs sTys j
          fun c' answers' frontier' svals => do
            let v := mkAppN (mkConst sc slvls) (sparams ++ svals)
            go c' answers' frontier' pfs ps pTys j (i + 1) (pvals.push v) k
        return mkAppN (mkConst `LeanScript.Term.record_casesOn')
          #[c.sg, c.gamma, info.τ, fsS, ← c.var ps[i].fvarId!, inner]
    | .union _ ulvls uparams uctors =>
        -- a union around the record: its dispatch, each branch binding the fields of its
        -- constructor, which are read in turn
        let .taggedUnion l ← tyView pTys[i]!
          | throwError "`#leanscript_to_term`: the tree of a union inside {info.ind} is not \
              a tagged union of the language"
        let mkBranch : BranchFn := fun minor _ payloadTys => do
          let ci ← natOfExpr minor
          let (cn, cfs) := uctors[ci]!
          recObjPayload info c answers frontier cfs payloadTys.toArray j
            fun c' answers' frontier' cvals =>
              let v := mkAppN (mkConst cn ulvls) (uparams ++ cvals)
              go c' answers' frontier' pfs ps pTys j (i + 1) (pvals.push v) k
        let minors := (Array.range uctors.size).map mkNatLit
        let cases ← mkTaggedUnionCases mkBranch c info.τ l 0 minors (uctors.map (·.1))
        return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn')
          #[c.sg, c.gamma, info.τ, l, ← c.var ps[i].fvarId!, cases]
    | .array arrTy elemTy elem =>
        -- an array of values that mention the record: a frontier value, whose own answer
        -- (if the recursion has one for it) is computed from the windows of its elements
        -- and bound
        withLocalDeclD `arr arrTy fun arrV => do
          let win ← c.var ps[i].fvarId!
          recObjBindArray info c answers arrV win pTys[i]! arrTy elemTy elem j
            fun c' answers' =>
              go c' answers' (frontier.push arrV) pfs ps pTys j (i + 1) (pvals.push arrV) k
    | .fn fTy dom =>
        -- the frontier: the function itself is a variable nothing may take apart, and the
        -- answer at `f a` is read from the window at `a`
        withLocalDeclD `fn fTy fun g => do
          if j == 0 then
            -- the window is the function of the answers
            go c (answers.push (fnKey g, ps[i])) (frontier.push g) pfs ps pTys j (i + 1)
              (pvals.push g) k
          else
            -- the window is the function of the answer trees: the function of the answers
            -- is bound beside it, `fun a => (window a).1`
            let .fn σ R ← tyView pTys[i]!
              | throwError "`#leanscript_to_term`: internal: the window of a function field \
                  of {info.ind} is not a function"
            let (τA, W) ← recObjTreeFields info R
            let ansTy := mkApp2 (mkConst ``LeanScript.TyWf.fn) σ τA
            -- `LeanScript.Term.fnTreeAnswer`, whose value `LeanScript.Term.eval_fnTreeAnswer`
            -- gives
            let ansT := mkAppN (mkConst `LeanScript.Term.fnTreeAnswer)
              #[c.sg, c.gamma, σ, τA, W, ← c.varIdx ps[i].fvarId!]
            withLocalDeclD `ansFn (← mkArrow dom info.τLean) fun ansF => do
              let cF := c.pushFields #[(ansF.fvarId!, ansTy)]
              let body ← go cF (answers.push (fnKey g, ansF)) (frontier.push g) pfs ps pTys j
                (i + 1) (pvals.push g) k
              return mkAppN (mkConst `LeanScript.Term.letE')
                #[c.sg, c.gamma, ansTy, info.τ, ansT, body]
    | .thunk _ =>
        -- the frontier: Lean holds the delay as `Thunk.mk g`, and the answer at `g ()` is
        -- the delayed answer forced
        let u ← getDecLevel info.selfTy
        withLocalDeclD `g (← mkArrow (mkConst ``Unit) info.selfTy) fun g => do
          let uτ ← getDecLevel info.τLean
          let v := mkApp2 (mkConst ``Thunk.mk [u]) info.selfTy g
          let force (d : Expr) := mkLambda `u .default (mkConst ``Unit)
            (mkApp2 (mkConst ``Thunk.get [uτ]) info.τLean d)
          if j == 0 then
            -- the window is the delayed answer
            go c (answers.push (fnKey g, force ps[i])) (frontier.push g) pfs ps pTys j (i + 1)
              (pvals.push v) k
          else
            -- the window is the delayed answer tree: the delayed answer is bound beside it,
            -- still delayed, `Thunk.mk (window.get).1`
            let .thunk R ← tyView pTys[i]!
              | throwError "`#leanscript_to_term`: internal: the window of a delayed field \
                  of {info.ind} is not a delay"
            let (τA, W) ← recObjTreeFields info R
            let ansTy := mkApp (mkConst ``LeanScript.TyWf.thunk) τA
            -- `LeanScript.Term.thunkTreeAnswer`, whose value
            -- `LeanScript.Term.eval_thunkTreeAnswer` gives
            let ansT := mkAppN (mkConst `LeanScript.Term.thunkTreeAnswer)
              #[c.sg, c.gamma, τA, W, ← c.varIdx ps[i].fvarId!]
            withLocalDeclD `ansThunk (mkApp (mkConst ``Thunk [uτ]) info.τLean) fun ansD => do
              let cD := c.pushFields #[(ansD.fvarId!, ansTy)]
              let body ← go cD (answers.push (fnKey g, force ansD)) (frontier.push g) pfs ps
                pTys j (i + 1) (pvals.push v) k
              return mkAppN (mkConst `LeanScript.Term.letE')
                #[c.sg, c.gamma, ansTy, info.τ, ansT, body]
    | .self =>
        if j == 0 then
          -- the frontier: the answer is bound, the subvalue is a variable nothing may
          -- take apart
          withLocalDeclD `sub info.selfTy fun g =>
            go c (answers.push (g, ps[i])) (frontier.push g) pfs ps pTys j (i + 1)
              (pvals.push g) k
        else
          let .record fsT ← tyView pTys[i]!
            | throwError "`#leanscript_to_term`: internal: an answer tree is not a record"
          let tTys := (← recordFieldTys fsT).toArray
          let some wTy := tTys[1]?
            | throwError "`#leanscript_to_term`: internal: an answer tree has no window"
          withLocalDeclD `ans info.τLean fun ans => do
            let wv ← mkFreshFVarId
            let c2 := c.pushFields #[(ans.fvarId!, tTys[0]!), (wv, wTy)]
            let inner ← recObjLevel info c2 answers frontier wv wTy (j - 1)
              fun c3 answers3 frontier3 subVals => do
                let sub := info.mkValue subVals
                go c3 (answers3.push (sub, ans)) frontier3 pfs ps pTys j (i + 1)
                  (pvals.push sub) k
            return mkAppN (mkConst `LeanScript.Term.record_casesOn')
              #[c.sg, c.gamma, info.τ, fsT, ← c.var ps[i].fvarId!, inner]
  else
    k c answers frontier pvals

/-- The answers of the recursion at an array `arrV` (of Lean type `arrTy` = `Array elemTy`)
    of values that mention the record, whose window `win` (of language type `winTy`) holds
    the windows of its elements, each of depth `j`: the answer of the auxiliary motive of
    `List elemTy` at its list, if the recursion has one (`recObjListAnswer`), and then that
    of the motive of `Array elemTy` at it (`recObjArrAnswer`), each let-bound in front of
    what `cont` builds, with `answers` extended by them. -/
partial def recObjBindArray (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (arrV win winTy arrTy elemTy : Expr) (elem : RecObjPayloadField) (j : Nat)
    (cont : TCtx → Array (Expr × Expr) → MetaM Expr) : MetaM Expr := do
  let u ← getDecLevel elemTy
  let aux? ← recObjAuxMotive info arrTy
  let list? ← recObjAuxMotive info (mkApp (mkConst ``List [u]) elemTy)
  let listOfArr := mkApp2 (mkConst ``Array.toList [u]) elemTy arrV
  -- the answer at the list inside the array, if the recursion has one for lists
  let withList (cont' : TCtx → Array (Expr × Expr) → Option (Nat × Expr) → MetaM Expr) :
      MetaM Expr := do
    match list? with
    | none => cont' c answers none
    | some (mL, τLLean) =>
        let τL ← tyOfType τLLean
        let listT ← recObjListAnswer info c win winTy elemTy elem j mL τLLean
        withLocalDeclD `ansList τLLean fun ansL => do
          let cL := c.pushFields #[(ansL.fvarId!, τL)]
          let body ← cont' cL (answers.push (motiveKey mL listOfArr, ansL)) (some (mL, ansL))
          return mkAppN (mkConst `LeanScript.Term.letE')
            #[c.sg, c.gamma, τL, info.τ, listT, body]
  withList fun cL answersL ansL? => do
    -- then the answer at the array, if the recursion has one for arrays
    match aux? with
    | none => cont cL answersL
    | some (mA, τALean) =>
        let τA ← tyOfType τALean
        let arrT ← recObjArrAnswer info cL elemTy mA ansL?
        withLocalDeclD `ansArr τALean fun ansA => do
          let cA := cL.pushFields #[(ansA.fvarId!, τA)]
          let body ← cont cA (answersL.push (motiveKey mA arrV, ansA))
          return mkAppN (mkConst `LeanScript.Term.letE')
            #[c.sg, cL.gamma, τA, info.τ, arrT, body]

/-- The answer of the auxiliary motive of `List elemTy` at the list of an array field, as
    a term in `c`: the array `win` of the window holds the windows of the elements (of
    depth `j`), and the answer is the fold of that array, `array_rec 0`, by the branches
    of the motive of `List elemTy` — each given the answer at the tail and, taken apart
    as `elem` says, the head's window: for an element that is the record, its answer;
    for one that holds the record (`Array Tree`, `Option Tree`), its fields, with the
    answers at what it holds.  The tail and whatever is left of the head are frontier
    values. -/
partial def recObjListAnswer (info : RecObjInfo) (c : TCtx) (win winTy elemTy : Expr)
    (elem : RecObjPayloadField) (j : Nat) (mL : Nat) (τLLean : Expr) : MetaM Expr := do
  let trans := info.trans
  let τL ← tyOfType τLLean
  let .array σ ← tyView winTy
    | throwError "`#leanscript_to_term`: internal: the window of an array field is not an array"
  let u ← getDecLevel elemTy
  let listTy := mkApp (mkConst ``List [u]) elemTy
  -- the empty list
  let nilV := mkApp (mkConst ``List.nil [u]) elemTy
  let nilBody ← recObjBranchBody info info.brecFs[mL]! info.motives nilV #[] #[]
  let nilT ← trans c nilBody
  let isSelf := elem matches .self
  -- a head and a tail, whose answers the fold of the array gives
  -- the Lean type of the head's window, where it is a value Lean can type: the answer
  -- (an element that is the record), the function of the answers or the delayed answer,
  -- at depth `0`
  let headTy ← match elem, j with
    | .self, 0 => pure info.τLean
    | .fn _ dom, 0 => mkArrow dom info.τLean
    | .thunk _, 0 => mkAppM ``Thunk #[info.τLean]
    | _, _ => pure (mkConst ``Unit)
  let consT ← withLocalDeclD `head headTy fun hd =>
    withLocalDeclD `tail (mkConst ``Unit) fun tl =>
    withLocalDeclD `ih τLLean fun ih =>
    withLocalDeclD `ts listTy fun ts => do
      let cC := c.pushFields #[(hd.fvarId!, σ),
        (tl.fvarId!, mkApp (mkConst ``LeanScript.TyWf.array) σ), (ih.fvarId!, τL)]
      let inner (cB : TCtx) (hdV : Expr) (answersB : Array (Expr × Expr))
          (frontierB : Array Expr) : MetaM Expr := do
        let consV := mkApp3 (mkConst ``List.cons [u]) elemTy hdV ts
        let body ← recObjBranchBody info info.brecFs[mL]! info.motives consV
          (answersB.push (motiveKey mL ts, ih)) (frontierB.push ts)
        trans cB body
      if isSelf then
        withLocalDeclD `t info.selfTy fun t => do
        if j == 0 then
          inner cC t #[(t, hd)] #[t]
        else
          -- the head is an answer tree: its answer is the first field
          let .record fsT ← tyView σ
            | throwError "`#leanscript_to_term`: internal: an answer tree is not a record"
          let tTys := (← recordFieldTys fsT).toArray
          withLocalDeclD `ans info.τLean fun ans =>
          withLocalDeclD `win (mkConst ``Unit) fun w => do
            let c2 := cC.pushFields #[(ans.fvarId!, tTys[0]!), (w.fvarId!, tTys[1]!)]
            let b ← inner c2 t #[(t, ans)] #[t]
            return mkAppN (mkConst `LeanScript.Term.record_casesOn')
              #[c.sg, cC.gamma, τL, fsT, ← cC.var hd.fvarId!, b]
      else
        -- the head's window, taken apart as the element type says
        let info' := { info with τ := τL }
        recObjPayloadFrom info' cC #[] #[] #[elem] #[hd] #[σ] j 0 #[]
          fun cB answersB frontierB vals => inner cB vals[0]! answersB frontierB
  let bases := mkAppN (mkConst `LeanScript.ArrayRecBases.nil) #[c.sg, c.gamma, σ, τL, nilT]
  return mkAppN (mkConst `LeanScript.Term.array_rec')
    #[c.sg, c.gamma, σ, τL, mkNatLit 0, win, bases, consT]

end

end LeanScript.ToTerm

end

end
