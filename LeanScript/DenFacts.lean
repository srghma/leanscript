module

public import LeanScript.Den

@[expose] public section

set_option autoImplicit false

/-!
# A value of a declared datatype is a value of its unfolded body

* `DSig.dataOut_dataIn`: taking one layer off a value built by `DSig.dataIn` gives back the
  unfolded body it was built from;
* `DSig.dataIn_dataOut`: putting back the layer `DSig.dataOut` took off gives back the value.

Both hold at every block of every signature, so `DSig.dataIn` and `DSig.dataOut` are
inverse bijections between `Ty.Den Δ (.data r)` and `Ty.Den Δ (unfold r)`.  The proofs go
through the transports (`Ty.lift_lower`, `Ty.lower_lift`), the round trips of one layer
(`Mems.unrollMember_rollMember`, `Mems.rollMember_unrollMember`) and the identity
transports of `DSig.block`.
-/

namespace LeanScript



section Transport
variable {ks ks' : List Nat} (f : Ref ks → Ref ks') (E : Ref ks' → Type)

mutual
theorem Ty.lift_lower : (t : Ty ks) → (x : Ty.den E (Ty.map f t)) →
    Ty.lift f E t (Ty.lower f E t x) = x
  | .prim _ _, _ => rfl
  | .fn a b, x => by
      funext y
      show Ty.lift f E b (Ty.lower f E b (x (Ty.lift f E a (Ty.lower f E a y)))) = x y
      rw [Ty.lift_lower a y, Ty.lift_lower b]
  | .array t, x => by
      have key : ∀ y : Array _, (y.map (Ty.lower f E t)).map (Ty.lift f E t) = y := by
        intro y
        rw [Array.map_map]
        conv => rhs; rw [← Array.map_id y]
        congr 1
        funext z
        exact Ty.lift_lower t z
      exact key x
  | .enum _, _ => rfl
  | .record t fs, x => by
      show (Ty.lift f E t (Ty.lower f E t x.1), Fields.lift f E fs (Fields.lower f E fs x.2)) = x
      rw [Ty.lift_lower t, Fields.lift_lower fs]; exact rfl
  | .union cs (h := _), x => Ctors.lift_lower cs x
  | .data _, _ => rfl
theorem Ty.lower_lift : (t : Ty ks) → (x : Ty.den (fun r => E (f r)) t) →
    Ty.lower f E t (Ty.lift f E t x) = x
  | .prim _ _, _ => rfl
  | .fn a b, x => by
      funext y
      show Ty.lower f E b (Ty.lift f E b (x (Ty.lower f E a (Ty.lift f E a y)))) = x y
      rw [Ty.lower_lift a y, Ty.lower_lift b]
  | .array t, x => by
      have key : ∀ y : Array _, (y.map (Ty.lift f E t)).map (Ty.lower f E t) = y := by
        intro y
        rw [Array.map_map]
        conv => rhs; rw [← Array.map_id y]
        congr 1
        funext z
        exact Ty.lower_lift t z
      exact key x
  | .enum _, _ => rfl
  | .record t fs, x => by
      show (Ty.lower f E t (Ty.lift f E t x.1), Fields.lower f E fs (Fields.lift f E fs x.2)) = x
      rw [Ty.lower_lift t, Fields.lower_lift fs]; exact rfl
  | .union cs (h := _), x => Ctors.lower_lift cs x
  | .data _, _ => rfl
theorem Fields.lift_lower : (fs : Fields ks) → (x : Fields.den E (Fields.map f fs)) →
    Fields.lift f E fs (Fields.lower f E fs x) = x
  | .one t, x => Ty.lift_lower t x
  | .cons t fs, x => by
      show (Ty.lift f E t (Ty.lower f E t x.1), Fields.lift f E fs (Fields.lower f E fs x.2)) = x
      rw [Ty.lift_lower t, Fields.lift_lower fs]; exact rfl
theorem Fields.lower_lift : (fs : Fields ks) → (x : Fields.den (fun r => E (f r)) fs) →
    Fields.lower f E fs (Fields.lift f E fs x) = x
  | .one t, x => Ty.lower_lift t x
  | .cons t fs, x => by
      show (Ty.lower f E t (Ty.lift f E t x.1), Fields.lower f E fs (Fields.lift f E fs x.2)) = x
      rw [Ty.lower_lift t, Fields.lower_lift fs]; exact rfl
theorem Ctors.lift_lower {bs : List Bool} : (cs : Ctors ks bs) → (x : Ctors.den E (Ctors.map f cs)) →
    Ctors.lift f E cs (Ctors.lower f E cs x) = x
  | .two .nullary .nullary, _ => rfl
  | .two .nullary (.fields fd), x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Fields.lift_lower fd a)
  | .two (.fields fc) .nullary, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Fields.lift_lower fc a)
  | .two (.fields fc) (.fields fd), x => by
      cases x with
      | inl a => exact congrArg Sum.inl (Fields.lift_lower fc a)
      | inr b => exact congrArg Sum.inr (Fields.lift_lower fd b)
  | .cons .nullary cs, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Ctors.lift_lower cs a)
  | .cons (.fields fc) cs, x => by
      cases x with
      | inl a => exact congrArg Sum.inl (Fields.lift_lower fc a)
      | inr b => exact congrArg Sum.inr (Ctors.lift_lower cs b)
theorem Ctors.lower_lift {bs : List Bool} : (cs : Ctors ks bs) → (x : Ctors.den (fun r => E (f r)) cs) →
    Ctors.lower f E cs (Ctors.lift f E cs x) = x
  | .two .nullary .nullary, _ => rfl
  | .two .nullary (.fields fd), x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Fields.lower_lift fd a)
  | .two (.fields fc) .nullary, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Fields.lower_lift fc a)
  | .two (.fields fc) (.fields fd), x => by
      cases x with
      | inl a => exact congrArg Sum.inl (Fields.lower_lift fc a)
      | inr b => exact congrArg Sum.inr (Fields.lower_lift fd b)
  | .cons .nullary cs, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Ctors.lower_lift cs a)
  | .cons (.fields fc) cs, x => by
      cases x with
      | inl a => exact congrArg Sum.inl (Fields.lower_lift fc a)
      | inr b => exact congrArg Sum.inr (Ctors.lower_lift cs b)
end

end Transport

theorem listUnroll_listRoll {n : Nat} {c : IPF n} {X : Fin n → Type} {D : Type}
    (f : D → c.Obj X) (g : c.Obj X → D) (h : ∀ d, g (f d) = d) :
    ∀ l : List D, listUnroll g (listRoll f l).1 (listRoll f l).2 = l
  | [] => rfl
  | d :: ds => by
      show g ⟨(f d).1, fun b => (f d).2 b⟩ :: listUnroll g (listRoll f ds).1 (fun b => (listRoll f ds).2 b)
        = d :: ds
      rw [show (⟨(f d).1, fun b => (f d).2 b⟩ : c.Obj X) = f d from rfl, h d,
        show (fun b => (listRoll f ds).2 b) = (listRoll f ds).2 from rfl, listUnroll_listRoll f g h ds]

section Roll
variable {ks K : List Nat} (w : Ref ks → Ref K) (E' : Ref K → Type) {n : Nat} (σ : Fin n → Ty K)

theorem Fld.unroll_roll {g : Nat} : (f : Fld ks n g) → (x : Ty.den E' (Fld.inst w σ f)) →
    Fld.unroll w E' σ f (Fld.roll w E' σ f x) = x
  | .hole _ _, _ => rfl
  | .old t, x => Ty.lift_lower w E' t x
  | .array f, x => by
      have key : ∀ y : Array (Ty.den E' (Fld.inst w σ f)),
          (⟨listUnroll (fun o => Fld.unroll w E' σ f o)
            (listRoll (fun d => Fld.roll w E' σ f d) y.toList).1
            (listRoll (fun d => Fld.roll w E' σ f d) y.toList).2⟩ : Array _) = y := by
        intro y
        rw [listUnroll_listRoll _ _ (Fld.unroll_roll f)]
      exact key x
  | .fn a f, x => by
      funext y
      show Fld.unroll w E' σ f (Fld.roll w E' σ f (x (Ty.lift w E' a (Ty.lower w E' a y)))) = x y
      rw [Fld.unroll_roll f, Ty.lift_lower]

theorem Flds.unroll_roll {g : Nat} : (fs : Flds ks n g) → (x : Fields.den E' (Flds.inst w σ fs)) →
    Flds.unroll w E' σ fs (Flds.roll w E' σ fs x) = x
  | .one f, x => Fld.unroll_roll w E' σ f x
  | .cons f fs, x => by
      show (Fld.unroll w E' σ f (Fld.roll w E' σ f x.1), Flds.unroll w E' σ fs (Flds.roll w E' σ fs x.2)) = x
      rw [Fld.unroll_roll, Flds.unroll_roll fs]; exact rfl

theorem BCtor.unrollTwo_rollTwo {g g' : Nat} {a b : Bool} : (c : BCtor ks n g a) →
    (d : BCtor ks n g' b) →
    (x : twoT (Ctor.den E' (BCtor.inst w σ c)) (Ctor.den E' (BCtor.inst w σ d))) →
    BCtor.unrollTwo w E' σ c d (BCtor.rollTwo w E' σ c d x) = x
  | .nullary, .nullary, _ => rfl
  | .nullary, .fields fd, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Flds.unroll_roll w E' σ fd a)
  | .fields fc, .nullary, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (Flds.unroll_roll w E' σ fc a)
  | .fields fc, .fields fd, x => by
      cases x with
      | inl a => exact congrArg Sum.inl (Flds.unroll_roll w E' σ fc a)
      | inr b => exact congrArg Sum.inr (Flds.unroll_roll w E' σ fd b)

theorem BCtor.unrollCons_rollCons {g : Nat} {a : Bool} {R : IPF n} {RT : Type}
    (rest : RT → R.Obj (fun i => Ty.den E' (σ i))) (unrest : R.Obj (fun i => Ty.den E' (σ i)) → RT)
    (h : ∀ r, unrest (rest r) = r) : (c : BCtor ks n g a) →
    (x : consT (Ctor.den E' (BCtor.inst w σ c)) RT) →
    BCtor.unrollCons w E' σ unrest c (BCtor.rollCons w E' σ rest c x) = x
  | .nullary, x => by
      cases x with
      | none => rfl
      | some a => exact congrArg some (h a)
  | .fields fc, x => by
      cases x with
      | inl a => exact congrArg Sum.inl (Flds.unroll_roll w E' σ fc a)
      | inr b => exact congrArg Sum.inr (h b)

theorem BCtors.unroll_roll {bs : List Bool} : (cs : BCtors ks n bs) → (x : Ctors.den E' (BCtors.inst w σ cs)) →
    BCtors.unroll w E' σ cs (BCtors.roll w E' σ cs x) = x
  | .two c d, x => BCtor.unrollTwo_rollTwo w E' σ c d x
  | .cons c cs, x =>
      BCtor.unrollCons_rollCons w E' σ _ _ (BCtors.unroll_roll cs) c x

theorem Alts.unroll_roll {g : Nat} {bs : List Bool} : (u : Alts ks n g bs) → (x : Ctors.den E' (Alts.inst w σ u)) →
    Alts.unroll w E' σ u (Alts.roll w E' σ u x) = x
  | .two₁ c d, x => BCtor.unrollTwo_rollTwo w E' σ c d x
  | .two₂ c d, x => BCtor.unrollTwo_rollTwo w E' σ c d x
  | .here c cs, x => BCtor.unrollCons_rollCons w E' σ _ _ (BCtors.unroll_roll w E' σ cs) c x
  | .there c u, x => BCtor.unrollCons_rollCons w E' σ _ _ (Alts.unroll_roll u) c x

theorem Decl.unroll_roll {g : Nat} : (d : Decl ks n g) → (x : Ty.den E' (Decl.inst w σ d)) →
    Decl.unroll w E' σ d (Decl.roll w E' σ d x) = x
  | .wrap f _, x => Fld.unroll_roll w E' σ f x
  | .record f fs, x => by
      show (Fld.unroll w E' σ f (Fld.roll w E' σ f x.1), Flds.unroll w E' σ fs (Flds.roll w E' σ fs x.2)) = x
      rw [Fld.unroll_roll, Flds.unroll_roll]; exact rfl
  | .union u (h := _), x => Alts.unroll_roll w E' σ u x

theorem Mems.unrollMember_rollMember {g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    (x : Ty.den E' (Mems.instMember w σ bs i h)) →
    Mems.unrollMember w E' σ bs i h (Mems.rollMember w E' σ bs i h x) = x
  | .nil, _, h, _ => absurd h (by omega)
  | .cons d _, 0, _, x => Decl.unroll_roll w E' σ d x
  | .cons _ bs, i + 1, _, x => Mems.unrollMember_rollMember bs i _ x
end Roll

/-! ## The transports of `DSig.block` are inverse -/

theorem DSig.Block.toIW_ofIW : {ks : List Nat} → (Δ : DSig ks) → (b : BRef ks) →
    (i : Fin ((Δ.block b).k + 1)) → (x : IW (Mems.fam (fun r => DSig.refDen Δ ((Δ.block b).w (.there r)))
      (Δ.block b).bs) i) → (Δ.block b).toIW i ((Δ.block b).ofIW i x) = x
  | _, .cons _ _ _, .here, _, _ => rfl
  | _, .cons Δ _ _, .there b, i, x => DSig.Block.toIW_ofIW Δ b i x

theorem DSig.Block.ofIW_toIW : {ks : List Nat} → (Δ : DSig ks) → (b : BRef ks) →
    (i : Fin ((Δ.block b).k + 1)) → (x : DSig.refDen Δ ((Δ.block b).w (.here i))) →
    (Δ.block b).ofIW i ((Δ.block b).toIW i x) = x
  | _, .cons _ _ _, .here, _, _ => rfl
  | _, .cons Δ _ _, .there b, i, x => DSig.Block.ofIW_toIW Δ b i x

theorem DSig.Block.map_ofIW_dest {ks : List Nat} (Δ : DSig ks) (b : BRef ks)
    (j : Fin ((Δ.block b).k + 1))
    (o : (Mems.fam (fun r => DSig.refDen Δ ((Δ.block b).w (.there r))) (Δ.block b).bs j).Obj
      (fun i => DSig.refDen Δ ((Δ.block b).w (.here i)))) :
    ((Δ.block b).toIW j ((Δ.block b).ofIW j
      (IW.mk j o.1 (fun p => (Δ.block b).toIW _ (o.2 p))))).dest.map
        (fun i y => (Δ.block b).ofIW i y) = o := by
  rw [DSig.Block.toIW_ofIW]
  simp only [IW.dest, IPF.Obj.map, DSig.Block.ofIW_toIW]
  rfl

/-- **One layer out after one layer in is the identity**, at every block of every
    signature. -/
theorem DSig.dataOut_dataIn {ks : List Nat} (Δ : DSig ks) (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (x : Ty.Den Δ ((Δ.block b).unfold j)) : Δ.dataOut b j (Δ.dataIn b j x) = x := by
  have h := DSig.Block.map_ofIW_dest Δ b j (Mems.rollMember (Δ.block b).old (DSig.refDen Δ)
    (fun i => .data ((Δ.block b).ref i)) (Δ.block b).bs j.val (Fin.zero_add_lt' j) x)
  refine (congrArg (Mems.unrollMember (Δ.block b).old (DSig.refDen Δ)
    (fun i => .data ((Δ.block b).ref i)) (Δ.block b).bs j.val (Fin.zero_add_lt' j)) h).trans ?_
  exact Mems.unrollMember_rollMember _ _ _ _ _ _ x

/-! ## One layer in after one layer out is the identity -/

theorem IPF.Obj.ext_snd {n : Nat} {P : IPF n} {X : Fin n → Type} {a : P.A}
    {f g : (b : P.B a) → X (P.tgt a b)} (h : ∀ b, f b = g b) :
    (⟨a, f⟩ : P.Obj X) = ⟨a, g⟩ := by
  have : f = g := funext h
  subst this; rfl

theorem listRoll_listUnroll {n : Nat} {c : IPF n} {X : Fin n → Type} {D : Type}
    (f : D → c.Obj X) (g : c.Obj X → D) (h : ∀ o, f (g o) = o) :
    ∀ (s : List c.A) (p : (b : ListPos c s) → X (ListPos.tgt c s b)),
      listRoll f (listUnroll g s p) = ⟨s, p⟩
  | [], p => IPF.Obj.ext_snd (P := ⟨List c.A, ListPos c, ListPos.tgt c⟩) (fun b => nomatch b)
  | a :: as, p => by
      simp only [listUnroll, listRoll]
      have e₁ := h ⟨a, fun b => p (.inl b)⟩
      have e₂ := listRoll_listUnroll f g h as (fun b => p (.inr b))
      revert e₁ e₂
      generalize f (g ⟨a, fun b => p (.inl b)⟩) = o₁
      generalize listRoll f (listUnroll g as (fun b => p (.inr b))) = o₂
      intro e₁ e₂
      subst e₁ e₂
      exact IPF.Obj.ext_snd (P := ⟨List c.A, ListPos c, ListPos.tgt c⟩)
        (fun b => match b with | .inl _ => rfl | .inr _ => rfl)

theorem IPF.Obj.pair_fst_snd {n : Nat} {c d : IPF n} {X : Fin n → Type} (o : (IPF.prod c d).Obj X) :
    IPF.Obj.pair o.fst o.snd = o := by
  obtain ⟨⟨a, b⟩, f⟩ := o
  exact IPF.Obj.ext_snd (P := IPF.prod c d) (fun q => match q with | .inl _ => rfl | .inr _ => rfl)

theorem IPF.Obj.const_ext {n : Nat} {A : Type} {X : Fin n → Type} (o o' : (IPF.const (n := n) A).Obj X)
    (h : o.1 = o'.1) : o = o' := by
  obtain ⟨a, f⟩ := o
  obtain ⟨a', f'⟩ := o'
  cases h
  exact IPF.Obj.ext_snd (fun b => b.elim)

theorem IPF.Obj.opt_none_ext {n : Nat} {c : IPF n} {X : Fin n → Type} (o o' : (IPF.opt c).Obj X)
    (h : o.1 = Option.none) (h' : o'.1 = Option.none) : o = o' := by
  obtain ⟨a, f⟩ := o
  obtain ⟨a', f'⟩ := o'
  cases h
  cases h'
  exact IPF.Obj.ext_snd (P := IPF.opt c) (fun b => (b : PEmpty).elim)

theorem IPF.Obj.array_eq {n : Nat} {c : IPF n} {X : Fin n → Type} (s : List c.A)
    (p : (b : ListPos c s) → X (ListPos.tgt c s b))
    (o : (s : List c.A) × ((b : ListPos c s) → X (ListPos.tgt c s b))) (h : o = ⟨s, p⟩) :
    (⟨⟨o.1⟩, o.2⟩ : (IPF.array c).Obj X) = ⟨⟨s⟩, p⟩ := by
  subst h; rfl

section Roll
variable {ks K : List Nat} (w : Ref ks → Ref K) (E' : Ref K → Type) {n : Nat} (σ : Fin n → Ty K)

theorem Fld.roll_unroll {g : Nat} : (f : Fld ks n g) →
    (x : (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i))) →
    Fld.roll w E' σ f (Fld.unroll w E' σ f x) = x
  | .hole _ _, x => by obtain ⟨u, p⟩ := x; rfl
  | .old t, x => IPF.Obj.const_ext _ x (Ty.lower_lift w E' t x.1)
  | .array f, x => by
      obtain ⟨⟨s⟩, p⟩ := x
      exact IPF.Obj.array_eq (X := fun i => Ty.den E' (σ i)) s p _ (listRoll_listUnroll (fun d => Fld.roll w E' σ f d)
        (fun o => Fld.unroll w E' σ f o) (Fld.roll_unroll f) s p)
  | .fn a f, ⟨fa, p⟩ => by
      have key : ∀ (L : Ty.den (fun r => E' (w r)) a → Ty.den (fun r => E' (w r)) a),
          (∀ y, L y = y) →
          ∀ (R : (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i)) →
            (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i))), (∀ o, R o = o) →
          (⟨fun y => (R ⟨fa (L y), fun q => p ⟨L y, q⟩⟩).1,
            fun pr => (R ⟨fa (L pr.1), fun q => p ⟨L pr.1, q⟩⟩).2 pr.2⟩ :
            (IPF.fn (Ty.den (fun r => E' (w r)) a) (Fld.toIPF (fun r => E' (w r)) f)).Obj
              (fun i => Ty.den E' (σ i))) = ⟨fa, p⟩ := by
        intro L hL R hR
        obtain rfl : L = id := funext hL
        obtain rfl : R = id := funext hR
        rfl
      exact key (fun y => Ty.lower w E' a (Ty.lift w E' a y)) (Ty.lower_lift w E' a)
        (fun o => Fld.roll w E' σ f (Fld.unroll w E' σ f o)) (Fld.roll_unroll f)

theorem Flds.roll_unroll {g : Nat} : (fs : Flds ks n g) →
    (x : (Flds.toIPF (fun r => E' (w r)) fs).Obj (fun i => Ty.den E' (σ i))) →
    Flds.roll w E' σ fs (Flds.unroll w E' σ fs x) = x
  | .one f, x => Fld.roll_unroll w E' σ f x
  | .cons f fs, x => by
      exact (congr (congrArg IPF.Obj.pair (Fld.roll_unroll w E' σ f x.fst))
        (Flds.roll_unroll fs x.snd)).trans (IPF.Obj.pair_fst_snd x)

theorem BCtor.rollTwo_unrollTwo {g g' : Nat} {a b : Bool} : (c : BCtor ks n g a) →
    (d : BCtor ks n g' b) →
    (x : (IPF.twoC (BCtor.toIPF (fun r => E' (w r)) c) (BCtor.toIPF (fun r => E' (w r)) d)).Obj
      (fun i => Ty.den E' (σ i))) →
    BCtor.rollTwo w E' σ c d (BCtor.unrollTwo w E' σ c d x) = x
  | .nullary, .nullary, x => IPF.Obj.const_ext _ x rfl
  | .nullary, .fields fd, x => by
      obtain ⟨a, p⟩ := x
      cases a with
      | none => exact IPF.Obj.opt_none_ext _ _ rfl rfl
      | some a => exact congrArg IPF.Obj.some (Flds.roll_unroll w E' σ fd ⟨a, p⟩)
  | .fields fc, .nullary, x => by
      obtain ⟨a, p⟩ := x
      cases a with
      | none => exact IPF.Obj.opt_none_ext _ _ rfl rfl
      | some a => exact congrArg IPF.Obj.some (Flds.roll_unroll w E' σ fc ⟨a, p⟩)
  | .fields fc, .fields fd, x => by
      obtain ⟨a, p⟩ := x
      cases a with
      | inl a => exact congrArg IPF.Obj.inl (Flds.roll_unroll w E' σ fc ⟨a, p⟩)
      | inr a => exact congrArg IPF.Obj.inr (Flds.roll_unroll w E' σ fd ⟨a, p⟩)

theorem BCtor.rollCons_unrollCons {g : Nat} {a : Bool} {R : IPF n} {RT : Type}
    (rest : RT → R.Obj (fun i => Ty.den E' (σ i))) (unrest : R.Obj (fun i => Ty.den E' (σ i)) → RT)
    (h : ∀ o, rest (unrest o) = o) : (c : BCtor ks n g a) →
    (x : (IPF.consC (BCtor.toIPF (fun r => E' (w r)) c) R).Obj (fun i => Ty.den E' (σ i))) →
    BCtor.rollCons w E' σ rest c (BCtor.unrollCons w E' σ unrest c x) = x
  | .nullary, x => by
      obtain ⟨a, p⟩ := x
      cases a with
      | none => exact IPF.Obj.opt_none_ext _ _ rfl rfl
      | some a => exact congrArg IPF.Obj.some (h ⟨a, p⟩)
  | .fields fc, x => by
      obtain ⟨a, p⟩ := x
      cases a with
      | inl a => exact congrArg IPF.Obj.inl (Flds.roll_unroll w E' σ fc ⟨a, p⟩)
      | inr a => exact congrArg IPF.Obj.inr (h ⟨a, p⟩)

theorem BCtors.roll_unroll {bs : List Bool} : (cs : BCtors ks n bs) →
    (x : (BCtors.toIPF (fun r => E' (w r)) cs).Obj (fun i => Ty.den E' (σ i))) →
    BCtors.roll w E' σ cs (BCtors.unroll w E' σ cs x) = x
  | .two c d, x => BCtor.rollTwo_unrollTwo w E' σ c d x
  | .cons c cs, x => BCtor.rollCons_unrollCons w E' σ _ _ (BCtors.roll_unroll cs) c x

theorem Alts.roll_unroll {g : Nat} {bs : List Bool} : (u : Alts ks n g bs) →
    (x : (Alts.toIPF (fun r => E' (w r)) u).Obj (fun i => Ty.den E' (σ i))) →
    Alts.roll w E' σ u (Alts.unroll w E' σ u x) = x
  | .two₁ c d, x => BCtor.rollTwo_unrollTwo w E' σ c d x
  | .two₂ c d, x => BCtor.rollTwo_unrollTwo w E' σ c d x
  | .here c cs, x => BCtor.rollCons_unrollCons w E' σ _ _ (BCtors.roll_unroll w E' σ cs) c x
  | .there c u, x => BCtor.rollCons_unrollCons w E' σ _ _ (Alts.roll_unroll u) c x

theorem Decl.roll_unroll {g : Nat} : (d : Decl ks n g) →
    (x : (Decl.toIPF (fun r => E' (w r)) d).Obj (fun i => Ty.den E' (σ i))) →
    Decl.roll w E' σ d (Decl.unroll w E' σ d x) = x
  | .wrap f _, x => Fld.roll_unroll w E' σ f x
  | .record f fs, x => by
      exact (congr (congrArg IPF.Obj.pair (Fld.roll_unroll w E' σ f x.fst))
        (Flds.roll_unroll w E' σ fs x.snd)).trans (IPF.Obj.pair_fst_snd x)
  | .union u (h := _), x => Alts.roll_unroll w E' σ u x

theorem Mems.rollMember_unrollMember {g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    (x : (Mems.member (fun r => E' (w r)) bs i h).Obj (fun j => Ty.den E' (σ j))) →
    Mems.rollMember w E' σ bs i h (Mems.unrollMember w E' σ bs i h x) = x
  | .nil, _, h, _ => absurd h (by omega)
  | .cons d _, 0, _, x => Decl.roll_unroll w E' σ d x
  | .cons _ bs, i + 1, _, x => Mems.rollMember_unrollMember bs i _ x
end Roll

/-- **One layer in after one layer out is the identity**: together with
    `DSig.dataOut_dataIn`, a value of a declared datatype *is* a value of its unfolded
    body. -/
theorem DSig.dataIn_dataOut {ks : List Nat} (Δ : DSig ks) (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (v : Ty.Den Δ (.data ((Δ.block b).ref j))) : Δ.dataIn b j (Δ.dataOut b j v) = v := by
  have h := Mems.rollMember_unrollMember (Δ.block b).old (DSig.refDen Δ)
    (fun i => .data ((Δ.block b).ref i)) (Δ.block b).bs j.val (Fin.zero_add_lt' j)
    (((Δ.block b).toIW j v).dest.map (fun i y => (Δ.block b).ofIW i y))
  show (Δ.block b).ofIW j (IW.mk j
    (Mems.rollMember (Δ.block b).old (DSig.refDen Δ) (fun i => .data ((Δ.block b).ref i))
      (Δ.block b).bs j.val (Fin.zero_add_lt' j)
      (Mems.unrollMember (Δ.block b).old (DSig.refDen Δ) (fun i => .data ((Δ.block b).ref i))
        (Δ.block b).bs j.val (Fin.zero_add_lt' j)
        (((Δ.block b).toIW j v).dest.map (fun i y => (Δ.block b).ofIW i y)))).1
    (fun p => (Δ.block b).toIW _
      ((Mems.rollMember (Δ.block b).old (DSig.refDen Δ) (fun i => .data ((Δ.block b).ref i))
        (Δ.block b).bs j.val (Fin.zero_add_lt' j)
        (Mems.unrollMember (Δ.block b).old (DSig.refDen Δ) (fun i => .data ((Δ.block b).ref i))
          (Δ.block b).bs j.val (Fin.zero_add_lt' j)
          (((Δ.block b).toIW j v).dest.map (fun i y => (Δ.block b).ofIW i y)))).2 p))) = v
  revert h
  generalize Mems.rollMember (Δ.block b).old (DSig.refDen Δ) (fun i => .data ((Δ.block b).ref i))
      (Δ.block b).bs j.val (Fin.zero_add_lt' j)
      (Mems.unrollMember (Δ.block b).old (DSig.refDen Δ) (fun i => .data ((Δ.block b).ref i))
        (Δ.block b).bs j.val (Fin.zero_add_lt' j)
        (((Δ.block b).toIW j v).dest.map (fun i y => (Δ.block b).ofIW i y))) = o
  intro h
  subst h
  have e : ∀ t : IW (Mems.fam (fun r => DSig.refDen Δ ((Δ.block b).w (.there r))) (Δ.block b).bs) j,
      IW.mk j (t.dest.map (fun i y => (Δ.block b).ofIW i y)).1
        (fun p => (Δ.block b).toIW _ ((t.dest.map (fun i y => (Δ.block b).ofIW i y)).2 p)) = t := by
    intro t
    cases t with
    | mk _ a f =>
      simp only [IW.dest, IPF.Obj.map, DSig.Block.toIW_ofIW]
  exact (congrArg ((Δ.block b).ofIW j) (e _)).trans (DSig.Block.ofIW_toIW Δ b j v)



end LeanScript

end
