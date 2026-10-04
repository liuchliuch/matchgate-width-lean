import MatchgateWidth.OrderedAllLeftGadget

/-! # Exact holographic coordinate identity for arbitrary all-left gadgets

This is a sum-product identity, independent of planarity or rank. In
particular, its Boolean instance has literal same-word contractions. Turning
that finite network into an ordered planar matching graph is a separate step.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 400000
local instance (priority := 2000) holographyFinDecidableEq (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _
local instance (priority := 2000) holographySumDecidableEq (α β : Type*) : DecidableEq (α ⊕ β) := Classical.decEq _

section Reindex
variable {K V W D B : Type*} {P : V → Type*}
variable [Field K] [Fintype V] [Fintype W] [Fintype D] [Fintype B]
variable [∀ v, Fintype (P v)]

/-- Local port assignments and wire assignments are equivalent whenever the
incidence map is a bijection, including empty port and vertex sets. -/
def portAssignmentEquiv (e : Sigma P ≃ W) :
    ((v : V) → P v → D) ≃ (W → D) :=
  (Equiv.piCurry (fun _ _ => D)).symm.trans (Equiv.arrowCongr e (Equiv.refl D))

@[simp] theorem portAssignmentEquiv_apply (e : Sigma P ≃ W)
    (x : (v : V) → P v → D) (w : W) :
    portAssignmentEquiv e x w = x (e.symm w).1 (e.symm w).2 := rfl

/-- Expand a product of local transforms and reindex every local label by its
actual wire. This is the finite distributive law, with no order assumptions. -/
theorem prod_leftTransform_reindex (e : Sigma P ≃ W) (M : D → B → K)
    (F : (v : V) → (P v → D) → K) (z : W → B) :
    (∏ v, leftTransform M (F v) (fun i => z (e ⟨v,i⟩))) =
      ∑ x : W → D, (∏ v, F v (fun i => x (e ⟨v,i⟩))) *
        ∏ w, M (x w) (z w) := by
  classical
  simp only [leftTransform]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (portAssignmentEquiv e)
  intro x
  rw [Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    congr 1
    funext i
    change (fun q : Sigma P => x q.1 q.2) ⟨v,i⟩ =
      (fun q : Sigma P => x q.1 q.2) (e.symm (e ⟨v,i⟩))
    rw [e.symm_apply_apply]
  · rw [← Fintype.prod_sigma (fun q : Sigma P => M (x q.1 q.2) (z (e q)))]
    apply Fintype.prod_equiv e
    intro q
    change (fun q : Sigma P => M (x q.1 q.2) (z (e q))) q =
      M ((fun q : Sigma P => x q.1 q.2) (e.symm (e q))) (z (e q))
    rw [e.symm_apply_apply]

/-- The right transform has the same coefficient sum; only its argument type
is the domain rather than the Boolean-word alphabet. -/
theorem prod_rightTransform_reindex (e : Sigma P ≃ W) (M : D → B → K)
    (H : (v : V) → (P v → B) → K) (x : W → D) :
    (∏ v, rightTransform M (H v) (fun i => x (e ⟨v,i⟩))) =
      ∑ y : W → B, (∏ v, H v (fun i => y (e ⟨v,i⟩))) *
        ∏ w, M (x w) (y w) := by
  simpa only [rightTransform, leftTransform] using
    prod_leftTransform_reindex e (fun b d => M d b) H x

/-- Sum over a sum-indexed word, retaining its two independent parts. -/
theorem sum_sum_words {E P D K : Type*} [Fintype E] [Fintype P] [Fintype D]
    [AddCommMonoid K] (f : (E ⊕ P → D) → K) :
    (∑ x, f x) = ∑ e : E → D, ∑ b : P → D, f (Sum.elim e b) := by
  classical
  rw [← (Equiv.sumArrowEquivProdArrow E P D).symm.sum_comp f,
    Fintype.sum_prod_type]
  rfl

private theorem sum_reverse_three {A B C K : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid K]
    (f : A → B → C → K) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  classical
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

end Reindex

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n : ℕ}
variable {D B : Type} [Fintype D] [Fintype B]

/-- The original domain language obtained from a common base and actual
right preimages. The local domain tensors are not reconstructed by choice. -/
def domainLanguage (M : D → B → ℂ)
    (F : (l : S.LeftLabel) → (Fin (S.leftArity l) → D) → ℂ)
    (H : (l : S.RightLabel) → (Fin (S.rightArity l) → B) → ℂ) :
    LabelledLanguage S D where
  left := F
  right l := rightTransform M (H l)

/-- The transformed primitive language retains all block and local orders. -/
def liftedLanguage (M : D → B → ℂ)
    (F : (l : S.LeftLabel) → (Fin (S.leftArity l) → D) → ℂ)
    (H : (l : S.RightLabel) → (Fin (S.rightArity l) → B) → ℂ) :
    LabelledLanguage S B where
  left l := leftTransform M (F l)
  right := H

/-- **General all-left holographic identity.** Lifting the actual boundary
sum equals contracting all transformed primitive tensors. No rank, nonzero,
connectedness or planar assumption is needed for this exact coordinate equality.
Every internal word is used in the same order at its two incidences. -/
theorem leftTransform_value (I : AllLeftGadget S a b c n) (M : D → B → ℂ)
    (F : (l : S.LeftLabel) → (Fin (S.leftArity l) → D) → ℂ)
    (H : (l : S.RightLabel) → (Fin (S.rightArity l) → B) → ℂ) :
    leftTransform M (I.value (domainLanguage M F H)) =
      I.value (liftedLanguage M F H) := by
  classical
  funext z
  have hL (y : Fin c → B) := prod_leftTransform_reindex I.leftIncidence M
    (fun v => F (I.leftLabel v)) (Sum.elim y z)
  simp only [sum_sum_words, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at hL
  change (∑ q : Fin n → D, I.value (domainLanguage M F H) q * ∏ p, M (q p) (z p)) = _
  simp only [value_eq, domainLanguage, liftedLanguage]
  simp_rw [prod_rightTransform_reindex I.rightIncidence]
  -- The local left transforms are kept folded for the distributive-law lemma.
  change (∑ q : Fin n → D,
    (∑ x : Fin c → D,
      (∏ v, F (I.leftLabel v) (fun i => Sum.elim x q (I.leftIncidence ⟨v,i⟩))) *
      (∑ y : Fin c → B,
        (∏ v, H (I.rightLabel v) (fun i => y (I.rightIncidence ⟨v,i⟩))) *
        ∏ e, M (x e) (y e))) * ∏ p, M (q p) (z p)) =
    ∑ y : Fin c → B,
      (∏ v, leftTransform M (F (I.leftLabel v))
        (fun i => Sum.elim y z (I.leftIncidence ⟨v,i⟩))) *
      ∏ v, H (I.rightLabel v) (fun i => y (I.rightIncidence ⟨v,i⟩))
  simp_rw [hL, Finset.mul_sum, Finset.sum_mul]
  rw [sum_reverse_three]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro q _
  ring

end AllLeftGadget
end
end MatchgateWidth
