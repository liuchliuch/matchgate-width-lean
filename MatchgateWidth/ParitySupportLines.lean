import MatchgateWidth.ControlledNetworkParity
import Mathlib.Data.Fintype.BigOperators

/-! # Rank-one marker-parity supports are endpoint lines -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
variable {K J D : Type*} [Field K] [Fintype J] [Fintype D]

theorem parity_insert_sum (χ : D → ZMod 2) (j : J) (d : D)
    (a : {i : J // i ≠ j} → D) :
    (∑ i, χ (insertBoundaryCoordinate j d a i)) = χ d + ∑ i, χ (a i) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  simp only [insertBoundaryCoordinate_same]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [insertBoundaryCoordinate_ne _ _ _ _ i.property]

/-- Entries in one flattening column cannot both occupy opposite parities. -/
theorem TensorHasParity.slice_product_zero (χ : D → ZMod 2) {T : (J → D) → K}
    {ε : ZMod 2} (hT : TensorHasParity χ T ε) (j : J) (d e : D)
    (hde : χ d ≠ χ e) (a : {i : J // i ≠ j} → D) :
    portFlatten T j d a * portFlatten T j e a = 0 := by
  by_cases hd : portFlatten T j d a = 0
  · simp [hd]
  by_cases he : portFlatten T j e a = 0
  · simp [he]
  have h₁ := hT (insertBoundaryCoordinate j d a) hd
  have h₂ := hT (insertBoundaryCoordinate j e a) he
  rw [parity_insert_sum] at h₁ h₂
  exact (hde (add_right_cancel (h₁.trans h₂.symm))).elim

/-- A rank-at-most-one flattening cannot have nonzero rows of both marker
parities. This uses a genuine nonzero two-by-two minor, not a decomposition
assumption. -/
theorem TensorHasParity.qutrit_rank_one_endpoint {T : (J → Fin 3) → K}
    {ε : ZMod 2} (hT : TensorHasParity qutritMarkerParity T ε) (j : J)
    (hr : (portFlatten T j).rank ≤ 1) :
    (∀ a, portFlatten T j 0 a = 0) ∨ (∀ a, portFlatten T j 1 a = 0) := by
  by_cases h0 : ∀ a, portFlatten T j 0 a = 0
  · exact Or.inl h0
  push Not at h0
  obtain ⟨a,ha⟩ := h0
  right
  intro b
  by_contra hb
  have ha1 : portFlatten T j 1 a = 0 :=
    (mul_eq_zero.mp (hT.slice_product_zero qutritMarkerParity j 0 1 (by decide) a)).resolve_left ha
  have hb0 : portFlatten T j 0 b = 0 :=
    (mul_eq_zero.mp (hT.slice_product_zero qutritMarkerParity j 0 1 (by decide) b)).resolve_right hb
  have hdet : ((portFlatten T j).submatrix ![0,1] ![a,b]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [Matrix.submatrix_apply, ha1, hb0] using mul_ne_zero ha hb
  have hl := Matrix.rank_submatrix_le (portFlatten T j) ![0,1] ![a,b]
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hl
  omega

/-- A matrix supported in a single coordinate row has its column support in
that exact coordinate line. -/
theorem columnSupport_le_coordinateLine {C : Type*} [Fintype C]
    (A : Matrix (Fin 3) C K) (r : Fin 3) (hzero : ∀ d, d ≠ r → ∀ a, A d a = 0) :
    columnSupport A ≤ K ∙ Pi.single r (1 : K) := by
  rintro v ⟨u,rfl⟩
  apply Submodule.mem_span_singleton.mpr
  refine ⟨(A.mulVec u) r, ?_⟩
  ext d
  by_cases hd : d = r
  · subst d
    simp
  · simp [hd, Matrix.mulVec, dotProduct, hzero d hd]

/-- Within the zero-one plane, a rank-one parity support lies in one of its
fixed endpoint axes. The ambient qutrit basis is unchanged. -/
theorem TensorHasParity.qutrit_support_le_endpoint {T : (J → Fin 3) → K}
    {ε : ZMod 2} (hT : TensorHasParity qutritMarkerParity T ε) (j : J)
    (hr : (portFlatten T j).rank ≤ 1) (hz : ∀ a, portFlatten T j 2 a = 0) :
    columnSupport (portFlatten T j) ≤ K ∙ Pi.single 0 (1 : K) ∨
    columnSupport (portFlatten T j) ≤ K ∙ Pi.single 1 (1 : K) := by
  rcases hT.qutrit_rank_one_endpoint j hr with h0 | h1
  · right
    apply columnSupport_le_coordinateLine
    intro d hd a
    fin_cases d
    · exact h0 a
    · exact (hd rfl).elim
    · exact hz a
  · left
    apply columnSupport_le_coordinateLine
    intro d hd a
    fin_cases d
    · exact (hd rfl).elim
    · exact h1 a
    · exact hz a

end
end MatchgateWidth
