import MatchgateWidth.IndexedPolygonalTrimming
import MatchgateWidth.PolygonalCollarGeometry

namespace MatchgateWidth
noncomputable section
open Set

/-- The distance between two opposed radial cuts is an explicit positive
multiple of the original direction. -/
theorem radialSegmentCut_sub_reverse (x y : ℂ) (δ : ℝ) :
    radialSegmentCut y x δ - radialSegmentCut x y δ =
      (1-2*(δ/‖y-x‖)) • (y-x) := by
  simp only [radialSegmentCut, norm_sub_rev]
  module

theorem radialSegmentCut_sub_left (x y : ℂ) (δ : ℝ) :
    y-radialSegmentCut x y δ = (1-δ/‖y-x‖) • (y-x) := by
  simp only [radialSegmentCut]
  module

theorem radialSegmentCut_reverse_sub_right (x y : ℂ) (δ : ℝ) :
    radialSegmentCut y x δ-x = (1-δ/‖y-x‖) • (y-x) := by
  simp only [radialSegmentCut, norm_sub_rev]
  module

private theorem radial_fraction_lt_half {δ L : ℝ} (hδ : 0<δ) (hL : 3*δ<L) :
    δ/L < 1/2 := by
  have hpos : 0<L := by linarith
  apply (div_lt_iff₀ hpos).mpr
  linarith

/-- Starting at the radial cut and proceeding in a nonnegative multiple of the
old edge direction never reenters the open source collar. -/
theorem radialSegmentCut_segment_outside {x y b : ℂ} {δ κ : ℝ}
    (hne : x≠y) (hδ : 0≤δ) (hκ : 0≤κ)
    (hb : b-radialSegmentCut x y δ = κ • (y-x)) :
    ∀ z ∈ segment ℝ (radialSegmentCut x y δ) b, δ ≤ dist z x := by
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hL : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have heq : radialSegmentCut x y δ + t • (b-radialSegmentCut x y δ) - x =
      (δ/‖y-x‖+t*κ) • (y-x) := by
    rw [hb, radialSegmentCut]
    module
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (div_nonneg hδ hL.le) (mul_nonneg ht.1 hκ))]
  calc
    δ = (δ/‖y-x‖)*‖y-x‖ := (div_mul_cancel₀ _ hL.ne').symm
    _ ≤ (δ/‖y-x‖+t*κ)*‖y-x‖ := by
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg ht.1 hκ)) hL.le

/-- A segment leaving a radial cut in a strictly positive multiple of the
original direction contacts the closed collar only at that cut. -/
theorem radialSegmentCut_segment_closedBall_contact {x y b : ℂ} {δ κ : ℝ}
    (hne : x≠y) (hδ : 0≤δ) (hκ : 0<κ)
    (hb : b-radialSegmentCut x y δ = κ • (y-x)) :
    segment ℝ (radialSegmentCut x y δ) b ∩ Metric.closedBall x δ ⊆
      {radialSegmentCut x y δ} := by
  intro z hz
  obtain ⟨hzseg, hzball⟩ := hz
  rw [segment_eq_image'] at hzseg
  obtain ⟨t, ht, rfl⟩ := hzseg
  have hL : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have heq : radialSegmentCut x y δ + t • (b-radialSegmentCut x y δ) - x =
      (δ/‖y-x‖+t*κ) • (y-x) := by
    rw [hb, radialSegmentCut]
    module
  change dist (radialSegmentCut x y δ + t • (b-radialSegmentCut x y δ)) x ≤ δ at hzball
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (div_nonneg hδ hL.le) (mul_nonneg ht.1 hκ.le)),
    add_mul, div_mul_cancel₀ _ hL.ne'] at hzball
  have hmul : 0 < κ*‖y-x‖ := mul_pos hκ hL
  have hzero : t=0 := by nlinarith [ht.1]
  simp only [hzero, zero_smul, add_zero, Set.mem_singleton_iff]

namespace IndexedSimplePolygonalRoute
variable {U : Set ℂ} {x y : ℂ} (r : IndexedSimplePolygonalRoute U x y)

/-- A cut a prescribed distance from the source on its first edge. -/
def radialSourceCut (δ : ℝ) : ℂ :=
  radialSegmentCut (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ) δ
/-- A cut a prescribed distance from the target on its last edge. -/
def radialTargetCut (δ : ℝ) : ℂ :=
  radialSegmentCut (r.vertex r.lastEdge.succ) (r.vertex r.lastEdge.castSucc) δ

@[simp] theorem radialSourceCut_dist (δ : ℝ) (hδ : 0≤δ) :
    dist (r.radialSourceCut δ) x = δ := by
  simpa only [radialSourceCut, r.firstEdge_castSucc, r.source] using
    radialSegmentCut_dist (r.nonzero r.firstEdge) hδ
@[simp] theorem radialTargetCut_dist (δ : ℝ) (hδ : 0≤δ) :
    dist (r.radialTargetCut δ) y = δ := by
  simpa only [radialTargetCut, r.lastEdge_succ, r.target] using
    radialSegmentCut_dist (r.nonzero r.lastEdge).symm hδ

theorem radialSourceCut_mem_openSegment (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖) :
    r.radialSourceCut δ ∈
      openSegment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ) :=
  radialSegmentCut_mem_openSegment hδ (by linarith)

theorem radialTargetCut_mem_openSegment (δ : ℝ) (hδ : 0<δ)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    r.radialTargetCut δ ∈
      openSegment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ) := by
  rw [openSegment_symm]
  apply radialSegmentCut_mem_openSegment hδ
  rw [norm_sub_rev]
  linarith

theorem firstEdge_eq_lastEdge_of_one (hn : r.edgeCount=1) :
    r.firstEdge = r.lastEdge := by
  apply Fin.ext
  simp [hn]

/-- For one edge, the common-radius cuts are strictly separated because the
radius is less than one third of the edge length. -/
theorem radialCuts_ne_of_one (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hn : r.edgeCount=1) : r.radialSourceCut δ ≠ r.radialTargetCut δ := by
  have hcoef : 0 < 1-2*(δ/‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖) := by
    have := radial_fraction_lt_half hδ hfirst
    linarith
  intro heq
  have hdiff : r.radialTargetCut δ-r.radialSourceCut δ = 0 := sub_eq_zero.mpr heq.symm
  rw [radialTargetCut, radialSourceCut, ← r.firstEdge_eq_lastEdge_of_one hn,
    radialSegmentCut_sub_reverse] at hdiff
  exact (smul_ne_zero hcoef.ne' (sub_ne_zero.mpr (r.nonzero r.firstEdge).symm)) hdiff

/-- Automatic exact endpoint trimming at a common radius, including routes
consisting of just one edge. -/
def trimAtRadius (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    IndexedSimplePolygonalRoute U (r.radialSourceCut δ) (r.radialTargetCut δ) :=
  r.trimEndpoints (r.radialSourceCut δ) (r.radialTargetCut δ)
    (r.radialSourceCut_mem_openSegment δ hδ hfirst)
    (r.radialTargetCut_mem_openSegment δ hδ hlast)
    (r.radialCuts_ne_of_one δ hδ hfirst)

/-- The retained fraction of a first or last edge. -/
def radialTrimCoefficient (δ L : ℝ) : ℝ :=
  if r.edgeCount=1 then 1-2*(δ/L) else 1-δ/L

theorem radialTrimCoefficient_pos (δ L : ℝ) (hδ : 0<δ) (hL : 3*δ<L) :
    0 < r.radialTrimCoefficient δ L := by
  have h := radial_fraction_lt_half hδ hL
  unfold radialTrimCoefficient
  split_ifs <;> linarith

/-- The trimmed first direction is a strictly positive multiple of the original
first direction, so the tangent and the local orientation are unchanged. -/
theorem trimAtRadius_first_difference (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    (r.trimAtRadius δ hδ hfirst hlast).vertex (r.trimAtRadius δ hδ hfirst hlast).firstEdge.succ -
      (r.trimAtRadius δ hδ hfirst hlast).vertex (r.trimAtRadius δ hδ hfirst hlast).firstEdge.castSucc =
      r.radialTrimCoefficient δ ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖ •
        (r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc) := by
  change r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.firstEdge.succ -
    r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.firstEdge.castSucc = _
  rw [r.trimmedVertex_succ, r.trimmedVertex_castSucc]
  simp only [firstEdge_val, zero_add, ite_true]
  by_cases hn : r.edgeCount=1
  · rw [ite_eq_left hn.symm]
    simp only [radialTrimCoefficient, hn, ite_true]
    rw [radialSourceCut, radialTargetCut, ← r.firstEdge_eq_lastEdge_of_one hn]
    exact radialSegmentCut_sub_reverse _ _ _
  · rw [ite_eq_right (Ne.symm hn)]
    simp only [radialTrimCoefficient, hn, ite_false, radialSourceCut]
    exact radialSegmentCut_sub_left _ _ _

/-- The same positive-scalar tangent agreement holds at the target. -/
theorem trimAtRadius_last_difference (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    (r.trimAtRadius δ hδ hfirst hlast).vertex (r.trimAtRadius δ hδ hfirst hlast).lastEdge.succ -
      (r.trimAtRadius δ hδ hfirst hlast).vertex (r.trimAtRadius δ hδ hfirst hlast).lastEdge.castSucc =
      r.radialTrimCoefficient δ ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖ •
        (r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc) := by
  change r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.lastEdge.succ -
    r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.lastEdge.castSucc = _
  rw [r.trimmedVertex_succ, r.trimmedVertex_castSucc]
  have hend : r.lastEdge.val+1=r.edgeCount := by
    simp only [lastEdge_val]
    have := r.positive
    omega
  rw [ite_eq_left hend]
  by_cases hn : r.edgeCount=1
  · have hzero : r.lastEdge.val=0 := by simp [hn]
    rw [ite_eq_left hzero]
    simp only [radialTrimCoefficient, hn, ite_true]
    rw [radialSourceCut, radialTargetCut, r.firstEdge_eq_lastEdge_of_one hn]
    exact radialSegmentCut_sub_reverse _ _ _
  · have hzero : r.lastEdge.val≠0 := by
      simp only [lastEdge_val]
      have := r.positive
      omega
    rw [ite_eq_right hzero]
    simp only [radialTrimCoefficient, hn, ite_false, radialTargetCut]
    exact radialSegmentCut_reverse_sub_right _ _ _

/-- Every automatically trimmed edge is contained in its original edge. -/
theorem trimAtRadius_segment_subset (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖)
    (i : Fin r.edgeCount) :
    segment ℝ ((r.trimAtRadius δ hδ hfirst hlast).vertex i.castSucc)
      ((r.trimAtRadius δ hδ hfirst hlast).vertex i.succ) ⊆
      segment ℝ (r.vertex i.castSucc) (r.vertex i.succ) :=
  r.trimmed_segment_subset _ _
    (openSegment_subset_segment _ _ _ (r.radialSourceCut_mem_openSegment δ hδ hfirst))
    (openSegment_subset_segment _ _ _ (r.radialTargetCut_mem_openSegment δ hδ hlast)) i

theorem trimAtRadius_trace_subset (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    polygonalTrace (List.ofFn (r.trimAtRadius δ hδ hfirst hlast).vertex) ⊆
      polygonalTrace (List.ofFn r.vertex) :=
  r.trimEndpoints_trace_subset _ _ _ _ _

/-- The entire first trimmed edge stays outside the open source collar. -/
theorem trimAtRadius_first_segment_outside (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    ∀ z ∈ segment ℝ ((r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.castSucc)
      ((r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.succ), δ ≤ dist z x := by
  have hd := r.trimAtRadius_first_difference δ hδ hfirst hlast
  have hstart : (r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.castSucc =
      r.radialSourceCut δ := by
    change r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.firstEdge.castSucc = _
    simp
  change (r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.succ -
    (r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.castSucc = _ at hd
  rw [hstart] at hd ⊢
  have hh := radialSegmentCut_segment_outside (r.nonzero r.firstEdge) hδ.le
    (r.radialTrimCoefficient_pos δ _ hδ hfirst).le hd
  simpa only [r.firstEdge_castSucc, r.source, radialSourceCut] using hh

/-- The entire last trimmed edge stays outside the open target collar. -/
theorem trimAtRadius_last_segment_outside (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    ∀ z ∈ segment ℝ ((r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc)
      ((r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.succ), δ ≤ dist z y := by
  have hd := r.trimAtRadius_last_difference δ hδ hfirst hlast
  have hend : (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.succ =
      r.radialTargetCut δ := by
    change r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.lastEdge.succ = _
    rw [r.lastEdge_succ, r.trimmedVertex_last]
  change (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.succ -
    (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc = _ at hd
  rw [hend] at hd ⊢
  have hd' : (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc -
      r.radialTargetCut δ =
      r.radialTrimCoefficient δ ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖ •
        (r.vertex r.lastEdge.castSucc-r.vertex r.lastEdge.succ) := by
    calc
      _ = -(r.radialTargetCut δ -
          (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc) := by abel
      _ = _ := by rw [hd, ← smul_neg, neg_sub]
  have hh := radialSegmentCut_segment_outside (r.nonzero r.lastEdge).symm hδ.le
    (r.radialTrimCoefficient_pos δ _ hδ hlast).le hd'
  rw [segment_symm]
  simpa only [r.lastEdge_succ, r.target, radialTargetCut] using hh

/-- The first trimmed edge meets its closed source collar exactly at its designated cut. -/
theorem trimAtRadius_first_segment_closedBall_contact (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    segment ℝ ((r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.castSucc)
      ((r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.succ) ∩ Metric.closedBall x δ ⊆
        {r.radialSourceCut δ} := by
  have hd := r.trimAtRadius_first_difference δ hδ hfirst hlast
  have hstart : (r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.castSucc =
      r.radialSourceCut δ := by
    change r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.firstEdge.castSucc = _
    simp
  change (r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.succ -
    (r.trimAtRadius δ hδ hfirst hlast).vertex r.firstEdge.castSucc = _ at hd
  rw [hstart] at hd ⊢
  have hh := radialSegmentCut_segment_closedBall_contact (r.nonzero r.firstEdge) hδ.le
    (r.radialTrimCoefficient_pos δ _ hδ hfirst) hd
  simpa only [r.firstEdge_castSucc, r.source, radialSourceCut] using hh


/-- The last trimmed edge meets its closed target collar exactly at its designated cut. -/
theorem trimAtRadius_last_segment_closedBall_contact (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ < ‖r.vertex r.firstEdge.succ-r.vertex r.firstEdge.castSucc‖)
    (hlast : 3*δ < ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖) :
    segment ℝ ((r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc)
      ((r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.succ) ∩ Metric.closedBall y δ ⊆
        {r.radialTargetCut δ} := by
  have hd := r.trimAtRadius_last_difference δ hδ hfirst hlast
  have hend : (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.succ =
      r.radialTargetCut δ := by
    change r.trimmedVertex (r.radialSourceCut δ) (r.radialTargetCut δ) r.lastEdge.succ = _
    rw [r.lastEdge_succ, r.trimmedVertex_last]
  change (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.succ -
    (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc = _ at hd
  rw [hend] at hd ⊢
  have hd' : (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc -
      r.radialTargetCut δ =
      r.radialTrimCoefficient δ ‖r.vertex r.lastEdge.succ-r.vertex r.lastEdge.castSucc‖ •
        (r.vertex r.lastEdge.castSucc-r.vertex r.lastEdge.succ) := by
    calc
      _ = -(r.radialTargetCut δ -
          (r.trimAtRadius δ hδ hfirst hlast).vertex r.lastEdge.castSucc) := by abel
      _ = _ := by rw [hd, ← smul_neg, neg_sub]
  have hh := radialSegmentCut_segment_closedBall_contact (r.nonzero r.lastEdge).symm hδ.le
    (r.radialTrimCoefficient_pos δ _ hδ hlast) hd'
  rw [segment_symm]
  simpa only [r.lastEdge_succ, r.target, radialTargetCut] using hh

end IndexedSimplePolygonalRoute
end
end MatchgateWidth
