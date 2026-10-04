import MatchgateWidth.PolygonalRibbonGeometry
import Mathlib.Topology.MetricSpace.Thickening

/-! # Uniformly narrow polygonal ribbon lanes

Positive transverse determinants remain positive for sufficiently small signed
offsets. Compactness of a closed segment simultaneously keeps every shifted
wire in any prescribed open carrier. The finite-family theorem selects one
width for all segments, without assuming a pre-existing ribbon drawing.
-/
namespace MatchgateWidth
noncomputable section

/-- Positive endpoint transversality survives a two-sided interval of offsets. -/
theorem ribbon_transverse_radius (p q u v : ℂ)
    (hu : 0 < orientedArea (q-p) u) (hv : 0 < orientedArea (q-p) v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε →
      0 < orientedArea (ribbonDirection p q u v δ) u ∧
      0 < orientedArea (ribbonDirection p q u v δ) v := by
  have hcu : Continuous (fun δ : ℝ => orientedArea (ribbonDirection p q u v δ) u) := by
    unfold orientedArea ribbonDirection
    fun_prop
  have hcv : Continuous (fun δ : ℝ => orientedArea (ribbonDirection p q u v δ) v) := by
    unfold orientedArea ribbonDirection
    fun_prop
  have hO : IsOpen {δ : ℝ | 0 < orientedArea (ribbonDirection p q u v δ) u ∧
      0 < orientedArea (ribbonDirection p q u v δ) v} :=
    (isOpen_lt continuous_const hcu).inter (isOpen_lt continuous_const hcv)
  have h0 : (0 : ℝ) ∈ {δ : ℝ | 0 < orientedArea (ribbonDirection p q u v δ) u ∧
      0 < orientedArea (ribbonDirection p q u v δ) v} := by
    simpa [ribbonDirection] using And.intro hu hv
  obtain ⟨ε,hε,he⟩ := Metric.isOpen_iff.mp hO 0 h0
  refine ⟨ε,hε,?_⟩
  intro δ hδ
  apply he
  simpa [Metric.mem_ball, Real.dist_eq] using hδ

/-- The perturbation is exactly the interpolated transverse displacement. -/
theorem ribbonArc_sub_center (p q u v : ℂ) (δ : ℝ) (t : unitInterval) :
    ribbonArc p q u v δ t - straightArc p q t =
      δ • ((1 - (t : ℝ)) • u + (t : ℝ) • v) := by
  apply Complex.ext <;>
    simp [ribbonArc, straightArc, ribbonSection, 
      ] <;> ring

/-- A uniform elementary distance bound independent of the edge parameter. -/
theorem ribbonArc_dist_le (p q u v : ℂ) (δ : ℝ) (t : unitInterval) :
    dist (ribbonArc p q u v δ t) (straightArc p q t) ≤ |δ| * (‖u‖ + ‖v‖) := by
  rw [dist_eq_norm, ribbonArc_sub_center, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |δ| * (‖(1 - (t : ℝ)) • u‖ + ‖(t : ℝ) • v‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg δ)
    _ = |δ| * ((1 - (t : ℝ)) * ‖u‖ + (t : ℝ) * ‖v‖) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr t.property.2), abs_of_nonneg t.property.1]
    _ ≤ |δ| * (‖u‖ + ‖v‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg δ)
      have hu := mul_le_mul_of_nonneg_right (show 1 - (t : ℝ) ≤ 1 by linarith [t.property.1]) (norm_nonneg u)
      have hv := mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg v)
      linarith

/-- An entire narrow ribbon lies in any chosen open neighborhood of its
central closed segment. This includes both endpoint cross-sections. -/
theorem ribbon_carrier_radius (p q u v : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hseg : Set.range (straightArc p q) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε →
      Set.range (ribbonArc p q u v δ) ⊆ U := by
  obtain ⟨ρ,hρ,hsub⟩ := (isCompact_range (continuous_straightArc p q)).exists_thickening_subset_open hU hseg
  have hd : 0 < ‖u‖ + ‖v‖ + 1 := by positivity
  refine ⟨ρ / (‖u‖ + ‖v‖ + 1), div_pos hρ hd, ?_⟩
  intro δ hδ z hz
  obtain ⟨t,rfl⟩ := hz
  apply hsub
  rw [Metric.mem_thickening_iff]
  refine ⟨straightArc p q t, ⟨t,rfl⟩, ?_⟩
  have hb := (lt_div_iff₀ hd).mp hδ
  have hn := ribbonArc_dist_le p q u v δ t
  have hc : |δ| * (‖u‖ + ‖v‖) ≤ |δ| * (‖u‖ + ‖v‖ + 1) := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg δ)
    linarith
  exact hn.trans_lt (hc.trans_lt hb)

/-- One radius simultaneously guarantees geometric containment and both
transversality inequalities for a particular segment. -/
theorem ribbon_segment_radius (p q u v : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hseg : Set.range (straightArc p q) ⊆ U)
    (hu : 0 < orientedArea (q-p) u) (hv : 0 < orientedArea (q-p) v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε →
      (0 < orientedArea (ribbonDirection p q u v δ) u) ∧
      (0 < orientedArea (ribbonDirection p q u v δ) v) ∧
      Set.range (ribbonArc p q u v δ) ⊆ U := by
  obtain ⟨a,ha,hat⟩ := ribbon_transverse_radius p q u v hu hv
  obtain ⟨b,hb,hbt⟩ := ribbon_carrier_radius p q u v hU hseg
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro δ hδ
  exact ⟨(hat δ (lt_of_lt_of_le hδ (min_le_left _ _))).1,
    (hat δ (lt_of_lt_of_le hδ (min_le_left _ _))).2,
    hbt δ (lt_of_lt_of_le hδ (min_le_right _ _))⟩

/-- A finite set of polygonal segments admits a common positive ribbon width,
including the empty edge family. -/
theorem finite_ribbon_segment_radius {ι : Type*} [Fintype ι]
    (p q u v : ι → ℂ) (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hseg : ∀ i, Set.range (straightArc (p i) (q i)) ⊆ U i)
    (hu : ∀ i, 0 < orientedArea (q i-p i) (u i))
    (hv : ∀ i, 0 < orientedArea (q i-p i) (v i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε → ∀ i,
      (0 < orientedArea (ribbonDirection (p i) (q i) (u i) (v i) δ) (u i)) ∧
      (0 < orientedArea (ribbonDirection (p i) (q i) (u i) (v i) δ) (v i)) ∧
      Set.range (ribbonArc (p i) (q i) (u i) (v i) δ) ⊆ U i := by
  classical
  have hx (i : ι) := ribbon_segment_radius (p i) (q i) (u i) (v i) (hU i) (hseg i) (hu i) (hv i)
  choose ε hε hεspec using hx
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    exact ⟨1,by norm_num,fun _ _ i => isEmptyElim i⟩
  | inr hne =>
    obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image Finset.univ ε Finset.univ_nonempty
    exact ⟨ε i,hε i,fun δ hδ j => hεspec j δ (hδ.trans_le (hmin j (Finset.mem_univ j)))⟩

end
end MatchgateWidth
