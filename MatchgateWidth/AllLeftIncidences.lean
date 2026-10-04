import MatchgateWidth.OrderedAllLeftGadget
import MatchgateWidth.NetworkParity

/-! # Proper incidences of actual all-left gadgets -/
namespace MatchgateWidth
noncomputable section
local instance (priority := 2000) allLeftIncidencesFinDecidableEq (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _
local instance (priority := 2000) allLeftIncidencesSumDecidableEq (α β : Type*) : DecidableEq (α ⊕ β) := Classical.decEq _
namespace AllLeftGadget
variable {S : LabelledShape} {a b c n : ℕ}

/-- The actual left half-edge belonging to an internal edge. -/
def internalLeft (I : AllLeftGadget S a b c n) (e : Fin c) : Sigma I.Ports :=
  ⟨Sum.inl (I.leftIncidence.symm (Sum.inl e)).1,
    (I.leftIncidence.symm (Sum.inl e)).2⟩

/-- The actual right half-edge belonging to an internal edge. -/
def internalRight (I : AllLeftGadget S a b c n) (e : Fin c) : Sigma I.Ports :=
  ⟨Sum.inr (I.rightIncidence.symm e).1, (I.rightIncidence.symm e).2⟩

@[simp] theorem incidence_internalLeft (I : AllLeftGadget S a b c n) (e : Fin c) :
    I.incidence (I.internalLeft e).1 (I.internalLeft e).2 = Sum.inl e :=
  I.leftIncidence.apply_symm_apply _

@[simp] theorem incidence_internalRight (I : AllLeftGadget S a b c n) (e : Fin c) :
    I.incidence (I.internalRight e).1 (I.internalRight e).2 = Sum.inl e :=
  congrArg Sum.inl (I.rightIncidence.apply_symm_apply _)

theorem internal_ne (I : AllLeftGadget S a b c n) (e : Fin c) :
    I.internalLeft e ≠ I.internalRight e := by
  intro h
  have h' := congrArg Sigma.fst h
  exact Sum.inl_ne_inr h'

theorem internal_unique (I : AllLeftGadget S a b c n) (e : Fin c)
    (v : Fin a ⊕ Fin b) (i : I.Ports v) (hi : I.incidence v i = Sum.inl e) :
    (⟨v,i⟩ : Sigma I.Ports) = I.internalLeft e ∨
      (⟨v,i⟩ : Sigma I.Ports) = I.internalRight e := by
  cases v with
  | inl v =>
    left
    have h : (⟨v,i⟩ : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v))) =
        I.leftIncidence.symm (Sum.inl e) := I.leftIncidence.injective
      (hi.trans (I.leftIncidence.apply_symm_apply _).symm)
    exact congrArg (fun q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)) =>
      (⟨Sum.inl q.1,q.2⟩ : Sigma I.Ports)) h
  | inr v =>
    right
    have h : (⟨v,i⟩ : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v))) =
        I.rightIncidence.symm e := I.rightIncidence.injective
      ((Sum.inl.inj hi).trans (I.rightIncidence.apply_symm_apply _).symm)
    exact congrArg (fun q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)) =>
      (⟨Sum.inr q.1,q.2⟩ : Sigma I.Ports)) h

/-- Both incidence counts required by network parity follow from the gadget's
actual left and right incidence bijections. -/
theorem properNetworkIncidences (I : AllLeftGadget S a b c n) :
    ProperNetworkIncidences I.incidence := by
  classical
  constructor
  · intro e
    have hf : Finset.univ.filter (fun q : Sigma I.Ports => I.incidence q.1 q.2 = Sum.inl e) =
        {I.internalLeft e,I.internalRight e} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact I.internal_unique e q.1 q.2
      · rintro (rfl | rfl)
        · exact I.incidence_internalLeft e
        · exact I.incidence_internalRight e
    have hc : (Finset.univ.filter (fun q : Sigma I.Ports => I.incidence q.1 q.2 = Sum.inl e)).card = 2 := by
      rw [hf]
      simp [I.internal_ne e]
    convert hc using 1 <;> congr <;> exact Subsingleton.elim _ _
  · intro p
    have hf : Finset.univ.filter (fun q : Sigma I.Ports => I.incidence q.1 q.2 = Sum.inr p) =
        {⟨Sum.inl (I.boundaryVertex p),I.boundaryPort p⟩} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact I.boundary_unique p q.1 q.2
      · rintro rfl
        exact I.incidence_boundary p
    have hc : (Finset.univ.filter (fun q : Sigma I.Ports => I.incidence q.1 q.2 = Sum.inr p)).card = 1 := by
      rw [hf]
      exact Finset.card_singleton _
    convert hc using 1 <;> congr <;> exact Subsingleton.elim _ _

end AllLeftGadget
end
end MatchgateWidth
