import MatchgateWidth.OrderedAllLeftGadget

/-! # Exact scalar-wire endpoint indices for all-left graph substitution -/
namespace MatchgateWidth
noncomputable section
open scoped Classical

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} (I : AllLeftGadget S a b c n)

/-- Physical corridors reverse internal left positions. Dangling boundary
positions retain their original order. -/
def leftWirePosition (e : Fin c ⊕ Fin n) (k : Fin t) : Fin t :=
  Sum.elim (fun _ => k.rev) (fun _ => k) e

@[simp] theorem leftWirePosition_twice (e : Fin c ⊕ Fin n) (k : Fin t) :
    leftWirePosition e (leftWirePosition e k) = k := by cases e <;> simp [leftWirePosition]

def leftWireTwist : Equiv.Perm ((Fin c ⊕ Fin n) × Fin t) where
  toFun q := (q.1,leftWirePosition q.1 q.2)
  invFun q := (q.1,leftWirePosition q.1 q.2)
  left_inv q := by simp
  right_inv q := by simp

/-- Actual scalar left ports: reverse only the internal block positions.
The exposed boundary positions are unchanged and retain their inherited order. -/
def leftWireEquiv : ((Fin c ⊕ Fin n) × Fin t) ≃
    (Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)) :=
  leftWireTwist.trans ((Equiv.prodCongr I.leftIncidence.symm (Equiv.refl (Fin t))).trans
    ((Equiv.sigmaProdDistrib (fun v : Fin a => Fin (S.leftArity (I.leftLabel v))) (Fin t)).trans
      (Equiv.sigmaCongrRight (fun _ => finProdFinEquiv))))

/-- The right scalar block positions coincide with the global word positions. -/
def rightWireEquiv : (Fin c × Fin t) ≃
    (Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)) :=
  (Equiv.prodCongr I.rightIncidence.symm (Equiv.refl (Fin t))).trans
    ((Equiv.sigmaProdDistrib (fun v : Fin b => Fin (S.rightArity (I.rightLabel v))) (Fin t)).trans
      (Equiv.sigmaCongrRight (fun _ => finProdFinEquiv)))

/-- Scalar internal bridge indices map to their actual left local endpoints. -/
def internalLeftWire (w : Fin (c*t)) : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t) :=
  I.leftWireEquiv (Sum.inl (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2)

/-- Scalar internal bridge indices map to their actual right local endpoints. -/
def internalRightWire (w : Fin (c*t)) : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t) :=
  I.rightWireEquiv (finProdFinEquiv.symm w)

/-- External scalar boundary indices retain their actual local left positions. -/
def boundaryLeftWire (w : Fin (n*t)) : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t) :=
  I.leftWireEquiv (Sum.inr (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2)

theorem internalLeftWire_injective : Function.Injective (I.internalLeftWire (t := t)) := by
  intro x y h
  have h' := I.leftWireEquiv.injective h
  have h1 := Sum.inl.inj (congrArg Prod.fst h')
  have h2 := congrArg Prod.snd h'
  exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)

theorem internalRightWire_injective : Function.Injective (I.internalRightWire (t := t)) :=
  I.rightWireEquiv.injective.comp finProdFinEquiv.symm.injective

theorem boundaryLeftWire_injective : Function.Injective (I.boundaryLeftWire (t := t)) := by
  intro x y h
  have h' := I.leftWireEquiv.injective h
  have h1 := Sum.inr.inj (congrArg Prod.fst h')
  have h2 := congrArg Prod.snd h'
  exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)

theorem internal_boundary_wire_disjoint (x : Fin (c*t)) (y : Fin (n*t)) :
    I.internalLeftWire x ≠ I.boundaryLeftWire y := by
  intro h
  have h' := I.leftWireEquiv.injective h
  exact Sum.inl_ne_inr (congrArg Prod.fst h')

theorem leftWireEquiv_apply_incidence (v : Fin a)
    (i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) :
    I.leftWireEquiv (I.leftIncidence ⟨v,i⟩,k) =
      ⟨v,finProdFinEquiv (i,leftWirePosition (I.leftIncidence ⟨v,i⟩) k)⟩ := by
  exact congrArg (fun q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)) =>
    (⟨q.1,finProdFinEquiv (q.2,leftWirePosition (I.leftIncidence ⟨v,i⟩) k)⟩ :
      Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)))
    (I.leftIncidence.symm_apply_apply ⟨v,i⟩)

theorem rightWireEquiv_apply_incidence (v : Fin b)
    (i : Fin (S.rightArity (I.rightLabel v))) (k : Fin t) :
    I.rightWireEquiv (I.rightIncidence ⟨v,i⟩,k) = ⟨v,finProdFinEquiv (i,k)⟩ := by
  exact congrArg (fun q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)) =>
    (⟨q.1,finProdFinEquiv (q.2,k)⟩ : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)))
    (I.rightIncidence.symm_apply_apply ⟨v,i⟩)

theorem leftWireEquiv_symm_local (v : Fin a)
    (i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) :
    I.leftWireEquiv.symm ⟨v,finProdFinEquiv (i,k)⟩ = (I.leftIncidence ⟨v,i⟩,leftWirePosition (I.leftIncidence ⟨v,i⟩) k) := by
  have h := I.leftWireEquiv.symm_apply_apply
    (I.leftIncidence ⟨v,i⟩,leftWirePosition (I.leftIncidence ⟨v,i⟩) k)
  rw [I.leftWireEquiv_apply_incidence, leftWirePosition_twice] at h
  exact h

theorem rightWireEquiv_symm_local (v : Fin b)
    (i : Fin (S.rightArity (I.rightLabel v))) (k : Fin t) :
    I.rightWireEquiv.symm ⟨v,finProdFinEquiv (i,k)⟩ = (I.rightIncidence ⟨v,i⟩,k) := by
  have h := I.rightWireEquiv.symm_apply_apply (I.rightIncidence ⟨v,i⟩,k)
  rw [I.rightWireEquiv_apply_incidence] at h
  exact h

/-- Boundary/internal bridge deletion masks in actual left local order. -/
def leftWireBits (x : Fin (c*t) → Bool) (z : Fin (n*t) → Bool)
    (q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)) : Bool :=
  match I.leftWireEquiv.symm q with
  | (Sum.inl e,k) => x (finProdFinEquiv (e,k))
  | (Sum.inr p,k) => z (finProdFinEquiv (p,k))

/-- Right local positions carry the global bridge deletion bits unchanged. -/
def rightWireBits (x : Fin (c*t) → Bool)
    (q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)) : Bool :=
  x (finProdFinEquiv (I.rightWireEquiv.symm q))

theorem leftWireBits_local (x : Fin (c*t) → Bool) (z : Fin (n*t) → Bool)
    (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) :
    I.leftWireBits x z ⟨v,finProdFinEquiv (i,k)⟩ =
      Sum.elim (fun e => x (finProdFinEquiv (e,k.rev)))
        (fun p => z (finProdFinEquiv (p,k))) (I.leftIncidence ⟨v,i⟩) := by
  unfold leftWireBits
  rw [I.leftWireEquiv_symm_local]
  cases I.leftIncidence ⟨v,i⟩ <;> rfl

theorem rightWireBits_local (x : Fin (c*t) → Bool)
    (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v))) (k : Fin t) :
    I.rightWireBits x ⟨v,finProdFinEquiv (i,k)⟩ =
      x (finProdFinEquiv (I.rightIncidence ⟨v,i⟩,k)) := by
  unfold rightWireBits
  rw [I.rightWireEquiv_symm_local]

/-- The local left mask is exactly the union of selected boundary and internal
bridge endpoints, with no assumed coefficient identity. -/
theorem leftWireBits_eq_selected (x : Fin (c*t) → Bool) (z : Fin (n*t) → Bool)
    (q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)) :
    decide (q ∈ (bridgeBitsEquiv (Fin (n*t)) z).image I.boundaryLeftWire ∪
      (bridgeBitsEquiv (Fin (c*t)) x).image I.internalLeftWire) = I.leftWireBits x z q := by
  classical
  obtain ⟨⟨e,k⟩,rfl⟩ := I.leftWireEquiv.surjective q
  cases e with
  | inl e =>
    have hn : I.leftWireEquiv (Sum.inl e,k) ∉
        (bridgeBitsEquiv (Fin (n*t)) z).image I.boundaryLeftWire := by
      intro h
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
      exact Sum.inr_ne_inl (congrArg Prod.fst (I.leftWireEquiv.injective he))
    have hm : I.leftWireEquiv (Sum.inl e,k) ∈
        (bridgeBitsEquiv (Fin (c*t)) x).image I.internalLeftWire ↔ x (finProdFinEquiv (e,k)) = true := by
      constructor
      · intro h
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
        have h' := I.leftWireEquiv.injective he
        have hw' : w = finProdFinEquiv (e,k) := by
          apply finProdFinEquiv.symm.injective
          have h1 : (finProdFinEquiv.symm w).1 = e := Sum.inl.inj (congrArg Prod.fst h')
          have h2 : (finProdFinEquiv.symm w).2 = k := congrArg Prod.snd h'
          exact (Prod.ext h1 h2).trans (finProdFinEquiv.symm_apply_apply (e,k)).symm
        subst w
        simpa [bridgeBitsEquiv] using hw
      · intro hx
        apply Finset.mem_image.mpr
        refine ⟨finProdFinEquiv (e,k), by simpa [bridgeBitsEquiv] using hx, ?_⟩
        simp [internalLeftWire]
    simp only [Finset.mem_union, hn, false_or, hm, leftWireBits, Equiv.symm_apply_apply]
    cases x (finProdFinEquiv (e,k)) <;> rfl
  | inr p =>
    have hn : I.leftWireEquiv (Sum.inr p,k) ∉
        (bridgeBitsEquiv (Fin (c*t)) x).image I.internalLeftWire := by
      intro h
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
      exact Sum.inl_ne_inr (congrArg Prod.fst (I.leftWireEquiv.injective he))
    have hm : I.leftWireEquiv (Sum.inr p,k) ∈
        (bridgeBitsEquiv (Fin (n*t)) z).image I.boundaryLeftWire ↔ z (finProdFinEquiv (p,k)) = true := by
      constructor
      · intro h
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
        have h' := I.leftWireEquiv.injective he
        have hw' : w = finProdFinEquiv (p,k) := by
          apply finProdFinEquiv.symm.injective
          have h1 : (finProdFinEquiv.symm w).1 = p := Sum.inr.inj (congrArg Prod.fst h')
          have h2 : (finProdFinEquiv.symm w).2 = k := congrArg Prod.snd h'
          exact (Prod.ext h1 h2).trans (finProdFinEquiv.symm_apply_apply (p,k)).symm
        subst w
        simpa [bridgeBitsEquiv] using hw
      · intro hz
        apply Finset.mem_image.mpr
        refine ⟨finProdFinEquiv (p,k), by simpa [bridgeBitsEquiv] using hz, ?_⟩
        simp [boundaryLeftWire]
    simp only [Finset.mem_union, hn, or_false, hm, leftWireBits, Equiv.symm_apply_apply]
    cases z (finProdFinEquiv (p,k)) <;> rfl

theorem rightWireBits_eq_selected (x : Fin (c*t) → Bool)
    (q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)) :
    decide (q ∈ (bridgeBitsEquiv (Fin (c*t)) x).image I.internalRightWire) = I.rightWireBits x q := by
  classical
  obtain ⟨⟨e,k⟩,rfl⟩ := I.rightWireEquiv.surjective q
  have hm : I.rightWireEquiv (e,k) ∈
      (bridgeBitsEquiv (Fin (c*t)) x).image I.internalRightWire ↔ x (finProdFinEquiv (e,k)) = true := by
    constructor
    · intro h
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
      have h' := I.rightWireEquiv.injective he
      have hw' : w = finProdFinEquiv (e,k) := by
        apply finProdFinEquiv.symm.injective
        exact h'.trans (finProdFinEquiv.symm_apply_apply _).symm
      subst w
      simpa [bridgeBitsEquiv] using hw
    · intro hx
      refine Finset.mem_image.mpr ⟨finProdFinEquiv (e,k), by simpa [bridgeBitsEquiv] using hx, ?_⟩
      simp [internalRightWire]
  simp only [hm, rightWireBits, Equiv.symm_apply_apply]
  cases x (finProdFinEquiv (e,k)) <;> rfl

end AllLeftGadget
end
end MatchgateWidth
