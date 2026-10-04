import MatchgateWidth.ConnectionPrimeGeometry
import MatchgateWidth.LabelledCoverCompression

/-!
# Exact labelled compression from connection-prime support geometry

These are assembly theorems for the faithfully extracted support geometry.
The equality to the rowspace of the original base is explicit. No source
gadget-realization statement is encoded as a cover hypothesis.
-/
namespace MatchgateWidth
noncomputable section

/-- The original base's rowspace in the fixed subset-coefficient coordinates. -/
def baseSubsetSpace {E : Type*} {t : ℕ} (M : Matrix E (BooleanInput t) ℂ) :
    Submodule ℂ (SubsetSignature t ℂ) :=
  (Submodule.span ℂ (Set.range M.row)).map spinorSubsetEquiv.toLinearMap

theorem baseSubsetSpace_finrank {E : Type*} [Fintype E] {t : ℕ}
    (M : Matrix E (BooleanInput t) ℂ) : Module.finrank ℂ (baseSubsetSpace M) = M.rank := by
  unfold baseSubsetSpace
  rw [← (spinorSubsetEquiv.submoduleMap (Submodule.span ℂ (Set.range M.row))).finrank_eq]
  exact (Matrix.rank_eq_finrank_span_row M).symm

/-- The coefficient equivalence introduces no new support containment. -/
theorem baseSubsetSpace_le_iff {E : Type*} {r t : ℕ}
    (M : Matrix E (BooleanInput t) ℂ) (H : Matrix (BooleanInput r) (BooleanInput t) ℂ) :
    baseSubsetSpace M ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap ↔
      Submodule.span ℂ (Set.range M.row) ≤ orderedRowSpace H := by
  constructor
  · intro h u hu
    obtain ⟨v, hv, he⟩ := h ⟨u, hu, rfl⟩
    have hve : v = u := spinorSubsetEquiv.injective he
    exact hve ▸ hv
  · intro h
    exact Submodule.map_mono h

namespace LabelledCommonPresentation
variable {S : LabelledShape} {t : ℕ}

/-- Connection-prime geometric collapse constructs one width-at-most-three
presentation of the identical labelled language. -/
theorem connectionPrime_compression (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3) (g : RealizedMatchgateGeometry t)
    (hamb : g.ambient = baseSubsetSpace p.baseMatrix) (hprime : g.ConnectionPrime) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 2 ^ r ∧ H.rank ≤ 8 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) r,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language := by
  have hdim : Module.finrank ℂ g.ambient = 3 := by
    rw [hamb, baseSubsetSpace_finrank, hM]
  obtain ⟨r, hr, H, hH, hHr, hc⟩ := g.connectionPrime_cover hdim hprime
  have hcover : Submodule.span ℂ (Set.range p.base) ≤ orderedRowSpace H := by
    apply (baseSubsetSpace_le_iff p.baseMatrix H).mp
    exact hamb ▸ hc
  obtain ⟨q, hq, hl, he, heq⟩ := p.exists_exactly_equivalent_of_common_cover H hH hHr hcover
  refine ⟨r, hr, H, hH, hHr, ?_, q, hq, hl, he, heq⟩
  rw [hHr]
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr).trans (by norm_num)

/-- The two-plane branch constructs an identical language at width two,
with an actual rank-four exact cover. -/
theorem two_planes_compression (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3) (g : RealizedMatchgateGeometry t)
    (hamb : g.ambient = baseSubsetSpace p.baseMatrix)
    {P Q : Submodule ℂ (SubsetSignature t ℂ)}
    (hP : P ∈ g.planes) (hQ : Q ∈ g.planes) (hne : P ≠ Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 4 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) 2,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language := by
  have hdim : Module.finrank ℂ g.ambient = 3 := by
    rw [hamb, baseSubsetSpace_finrank, hM]
  obtain ⟨H, hH, hHr, hc⟩ := g.two_planes_cover hdim hP hQ hne
  have hcover : Submodule.span ℂ (Set.range p.base) ≤ orderedRowSpace H := by
    apply (baseSubsetSpace_le_iff p.baseMatrix H).mp
    exact hamb ▸ hc
  obtain ⟨q, hq, hl, he, heq⟩ := p.exists_exactly_equivalent_of_common_cover H hH hHr hcover
  exact ⟨H, hH, hHr, q, hq, hl, he, heq⟩

end LabelledCommonPresentation
end
end MatchgateWidth
