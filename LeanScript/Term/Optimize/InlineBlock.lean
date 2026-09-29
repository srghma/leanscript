module

public import LeanScript.Term.Optimize.Inline
public import LeanScript.Term.Rename.Relevel

@[expose] public section

set_option autoImplicit false

/-!
# Inlining the body of a known closure

A known closure with a closed body (`val k := fun x => (closed) body`) called on a neutral
argument (`let y := k a`) is replaced by its body, moved to the depth of the call
(`Term.relvl`), with the parameter renamed to `a` (bound first by `let x := share a` when `a` is
not an unknown):

* in tail position, `let y := k a; ret y` becomes the body itself (`BlockFn.applyNeu`);
* otherwise the body must be a straight line of `let`s ending in `ret e` with `e` neutral, and
  the rest of the statement is put after it, `let y := share e; rest` (`Term.bindRet`, in
  `LeanScript.Term.Optimize.InlineSubst`).

This file has the pieces: what is known about a closure (`BlockFn`, `BInfo`), the renaming of
its body to a call, and the splicing of a straight-line body in front of the rest.  The walk
that uses them is `Term.retWalk` (`LeanScript.Term.Optimize.InlineRet`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Known closures with a closed body -/

/-- A closure of type `ty = σ → τ` whose body is `body`, a statement at depth `D` over the known
    context `Φ` and the parameter (at level `D`). -/
structure BlockFn (Δ : DSig ks) (Φ : KCtx ks) (ty : Ty ks) where
  σ : Ty ks
  τ : Ty ks
  hty : ty = .fn σ τ
  u : Usage01ω
  D : Nat
  o : Lvl
  body : Term Δ D Φ [⟨σ, u, D⟩] τ [] o

/-- `f` describes the value `x` in the known environment `κ`. -/
def BlockFn.Sem {Φ : KCtx ks} {ty : Ty ks} (f : BlockFn Δ Φ ty) (κ : KEnv Δ Φ)
    (x : Ty.Den Δ ty) : Prop :=
  ∀ v : Ty.Den Δ f.σ, (cast (congrArg (Ty.Den Δ) f.hty) x : Ty.Den Δ (.fn f.σ f.τ)) v =
    f.body.eval κ (Tuple.cons v Tuple.nil) Tuple.nil

/-- Move the description along a renaming of the known values. -/
def BlockFn.rename {Φ Φ' : KCtx ks} (rk : KRen Φ Φ') {ty : Ty ks} (f : BlockFn Δ Φ ty) :
    Option (BlockFn Δ Φ' ty) :=
  (f.body.rename rk URen.id JRen.id).map fun b => ⟨f.σ, f.τ, f.hty, f.u, f.D, f.o, b⟩

/-- What is known about the bodies of the known closures in scope. -/
structure BInfo (Δ : DSig ks) (Φ : KCtx ks) : Type where
  /-- The body of a known closure, if known. -/
  get : ∀ {ty : Ty ks} {o : Lvl}, KVar Φ ty o → Option (BlockFn Δ Φ ty)

/-- Nothing is known. -/
def BInfo.empty {Φ : KCtx ks} : BInfo Δ Φ := ⟨fun _ => none⟩

/-- The lookup under one more known binder. -/
def BInfo.consGet {Φ : KCtx ks} (I : BInfo Δ Φ) :
    {b : KBinder ks} → Option (BlockFn Δ Φ b.ty) → {ty : Ty ks} → {o : Lvl} →
    KVar (b :: Φ) ty o → Option (BlockFn Δ (b :: Φ) ty)
  | _, new, _, _, .head => new.bind (·.rename KRen.wk1)
  | _, _, _, _, .tail k => (I.get k).bind (·.rename KRen.wk1)

/-- What is known under one more known binder, whose value is described by `new`. -/
def BInfo.cons {Φ : KCtx ks} {b : KBinder ks} (new : Option (BlockFn Δ Φ b.ty))
    (I : BInfo Δ Φ) : BInfo Δ (b :: Φ) :=
  ⟨fun k => I.consGet new k⟩

/-- Seen from a closed body. -/
def BInfo.toClosed {Φ : KCtx ks} (I : BInfo Δ Φ) : BInfo Δ (KCtx.closedOnly Φ) :=
  ⟨fun k => (I.get k.unmask).bind (·.rename (fun x => x.mask))⟩

/-- `I` describes the values of `κ`. -/
def BInfo.Agree {Φ : KCtx ks} (I : BInfo Δ Φ) (κ : KEnv Δ Φ) : Prop :=
  ∀ {ty : Ty ks} {o : Lvl} (k : KVar Φ ty o) (f : BlockFn Δ Φ ty), I.get k = some f →
    f.Sem κ (κ.get k)

/-- What a value tells about itself: a closure with a closed body. -/
def Val.blockFn? : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {ty : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ ty o → Option (BlockFn Δ Φ ty)
  | _, _, _, _, _, .lam (.closed t) =>
      (t.rename (fun x => some x.unmask) URen.id JRen.id).map
        fun t' => ⟨_, _, rfl, _, _, _, t'⟩
  | _, _, _, _, _, _ => none

/-! ## The body at a call -/

/-- The parameter, renamed to the unknown `x`. -/
def ULRen.single {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {D ℓx : Nat} (x : UVar Γ σ ℓx) :
    ULRen [⟨σ, u, D⟩] Γ
  | _, _, .head _ => some ⟨ℓx, x⟩
  | _, _, .tail y => nomatch y

/-- The same known values, their levels kept. -/
def KLRen.id {Φ : KCtx ks} : KLRen Φ Φ := fun k => some ⟨_, k⟩

/-- No join point in the body. -/
def JRen.ofNil {js : JCtx ks} : JRen [] js := fun j => nomatch j

/-- The body of `f`, at depth `d`, its parameter being the unknown `x`. -/
def BlockFn.applyVar {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓx : Nat} (f : BlockFn Δ Φ (.fn σ τ)) (x : UVar Γ σ ℓx) :
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o') :=
  match f with
  | ⟨σ', τ', _, _, _, _, body⟩ =>
      if hs : σ' = σ ∧ τ' = τ then
        (hs.2 ▸ hs.1 ▸ body : Term Δ _ Φ [⟨σ, _, _⟩] τ [] _).relvl (D' := d) KLRen.id
          (ULRen.single x) JRen.ofNil
      else none

/-- The body of `f`, at depth `d`, applied to the neutral expression `n`: the parameter is
    renamed to `n` when it is an unknown, otherwise `n` is shared first. -/
def BlockFn.applyNeu {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓn : Nat} (f : BlockFn Δ Φ (.fn σ τ)) : Neu Δ Φ Γ σ ℓn →
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | .var x => f.applyVar x
  | n => (f.applyVar (Γ := ⟨σ, Usage1ω.many.toUsage01ω, d⟩ :: Γ) (.head (by decide))).map
      fun r => ⟨_, .letE .many (.share n) r.2⟩

/-! ## Splicing a straight-line body in front of the rest -/

/-- Weakening by one unknown. -/
def URen.wk1 {Γ : UCtx ks} {b : UBinder ks} : URen Γ (b :: Γ) := fun x => some (.tail x)

/-- Weakening by the unknowns `bs`. -/
def URen.wkN {Γ : UCtx ks} : (bs : UCtx ks) → URen Γ (bs ++ Γ)
  | [] => URen.id
  | _ :: bs => fun x => (URen.wkN bs x).map .tail

/-- A total renaming of join points. -/
abbrev JMap (js js' : JCtx ks) : Type := ∀ {σ : Ty ks}, JVar js σ → JVar js' σ

/-- Under one more join point. -/
def JMap.lift {js js' : JCtx ks} (m : JMap js js') : (b : JBinder ks) → JMap (b :: js) (b :: js')
  | ⟨_, _⟩, _, .head => .head
  | ⟨_, _⟩, _, .tail x => .tail (m x)

mutual
/-- `t` with every answer `ret e` turned into a jump `jump j e` (and its jumps renamed by `m`):
    the answers of `t` go to the join point `j`. -/
def Term.retToJump {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {js js' : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ σ js o → JMap js js' → JVar js' σ →
    Term Δ d Φ Γ τ js' o
  | _, _, _, _, _, _, .ret e, _, j => .jump j e
  | _, _, _, _, _, _, .letV u v b, m, j => .letV u v (b.retToJump m j)
  | _, _, _, _, _, _, .letE u c b, m, j => .letE u c (b.retToJump m j)
  | _, _, _, _, _, _, .record_casesOn us n b, m, j => .record_casesOn us n (b.retToJump m j)
  | _, _, _, _, _, _, .branch br, m, j => .branch (br.retToJump m j)
  | _, _, _, _, _, _, .jump x e, m, _ => .jump (m x) e
/-- `Term.retToJump` in a branch. -/
def Branch.retToJump {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {js js' : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ σ js ℓ → JMap js js' → JVar js' σ →
    Branch Δ d Φ Γ τ js' ℓ
  | _, _, _, _, _, _, .ite c t e, m, j => .ite c (t.retToJump m j) (e.retToJump m j)
  | _, _, _, _, _, _, .enum_casesOn e bs, m, j => .enum_casesOn e (fun i => (bs i).retToJump m j)
  | _, _, _, _, _, _, .union_casesOn e bs, m, j => .union_casesOn e (bs.retToJump m j)
  | _, _, _, _, _, _, .join σ' u uₓ body main, m, j =>
      .join σ' u uₓ (body.retToJump m j) (main.retToJump (m.lift _) (.tail j))
/-- `Term.retToJump` in the branches of a union's case analysis. -/
def Branches.retToJump {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {js js' : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs σ js o → JMap js js' → JVar js' σ → Branches Δ d Φ Γ cs τ js' o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, m, j =>
      .two us₁ us₂ (b₁.retToJump m j) (b₂.retToJump m j)
  | _, _, _, _, _, _, _, _, .cons us b bs, m, j => .cons us (b.retToJump m j) (bs.retToJump m j)
end

/-- No join point to rename. -/
def JMap.ofNil {js : JCtx ks} : JMap [] js := fun x => nomatch x

end LeanScript

end
