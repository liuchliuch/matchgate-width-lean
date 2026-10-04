import MatchgateWidth.CompactRoutingSeparation
import MatchgateWidth.PolygonalPathRealization

/-! # Finite vertex collars and exact radial segment cuts -/
namespace MatchgateWidth
noncomputable section
open Set Metric

/-- Finitely many distinct points admit pairwise-disjoint closed round disks,
with one positive radius for the whole family. -/
theorem finite_points_disjoint_closedBalls {V : Type*} [Finite V]
    (p : V → ℂ) (hp : Function.Injective p) :
    ∃ r : ℝ, 0<r ∧ Pairwise (fun v w => Disjoint (closedBall (p v) r) (closedBall (p w) r)) := by
  classical
  obtain ⟨U,hU,hpU,_,hd⟩ := finite_compact_disjoint_open_neighborhoods
    (fun v => {p v}) (fun _ => Set.univ) (fun _ => isCompact_singleton)
    (fun v w hvw => Set.disjoint_singleton.mpr (fun h => hvw (hp h)))
    (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  choose ε hε he using fun v => Metric.isOpen_iff.mp (hU v) (p v) (hpU v (by simp))
  obtain ⟨r,hr,hre⟩ := finite_positive_lower_bound ε hε
  refine ⟨r/2,div_pos hr (by norm_num),?_⟩
  intro v w hvw
  apply (hd hvw).mono
  · intro z hz
    apply he v
    change dist z (p v) < ε v
    change dist z (p v) ≤ r/2 at hz
    apply lt_of_le_of_lt hz
    linarith [hre v]
  · intro z hz
    apply he w
    change dist z (p w) < ε w
    change dist z (p w) ≤ r/2 at hz
    apply lt_of_le_of_lt hz
    linarith [hre w]

/-- A common positive radius avoids every compact obstacle designated as
nonincident with a vertex; incident pieces need not be separated. -/
theorem finite_vertex_obstacle_radius {V ι : Type*} [Finite V] [Finite ι]
    (p : V → ℂ) (K : ι → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (Inc : V → ι → Prop) (havoid : ∀ v i, ¬Inc v i → p v ∉ K i) :
    ∃ r : ℝ, 0<r ∧ ∀ v i, ¬Inc v i → ∀ z∈K i, r<dist z (p v) := by
  classical
  let S : V → ι → Set ℂ := fun v i => if Inc v i then ∅ else K i
  have hS : ∀ v i, IsCompact (S v i) := by
    intro v i
    by_cases h : Inc v i <;> simp only [S,h,ite_true,ite_false]
    · exact isCompact_empty
    · exact hK i
  have hpS : ∀ v i, p v ∉ S v i := by
    intro v i
    by_cases h : Inc v i
    · simp [S,h]
    · simpa [S,h] using havoid v i h
  choose ε hε he using fun v => finite_compact_obstacles_avoid_ball (S v) (hS v) (p v) (hpS v)
  obtain ⟨r,hr,hre⟩ := finite_positive_lower_bound ε hε
  refine ⟨r/2,div_pos hr (by norm_num),?_⟩
  intro v i hi z hz
  have hh := he v i z (by simpa [S,hi] using hz)
  linarith [hre v]

/-- The point at distance `r` along the segment from `x` towards `y`. -/
def radialSegmentCut (x y : ℂ) (r : ℝ) : ℂ := x+(r/‖y-x‖)•(y-x)

theorem radialSegmentCut_dist {x y : ℂ} (hne : x≠y) {r : ℝ} (hr : 0≤r) :
    dist (radialSegmentCut x y r) x = r := by
  have hn : 0<‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  rw [radialSegmentCut,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr hn.le),div_mul_cancel₀ _ (ne_of_gt hn)]

/-- A positive cut shorter than the original segment lies strictly inside it. -/
theorem radialSegmentCut_mem_openSegment {x y : ℂ} {r : ℝ}
    (hr : 0<r) (hlen : r<‖y-x‖) : radialSegmentCut x y r ∈ openSegment ℝ x y := by
  have hn : 0<‖y-x‖ := hr.trans hlen
  refine ⟨1-r/‖y-x‖,r/‖y-x‖,sub_pos.mpr ((div_lt_one hn).mpr hlen),
    div_pos hr hn,by ring,?_⟩
  unfold radialSegmentCut
  module

/-- The remaining outward portion of a cut segment stays outside the open
round collar. The boundary cut point is permitted. -/
theorem radialSegmentCut_tail_outside {x y : ℂ} {r : ℝ}
    (hr : 0<r) (hlen : r<‖y-x‖) :
    ∀ z∈segment ℝ (radialSegmentCut x y r) y, r≤dist z x := by
  intro z hz
  have hn : 0<‖y-x‖ := hr.trans hlen
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have hcoef : r/‖y-x‖ ≤ (1-t)*(r/‖y-x‖)+t := by
    have hfrac := (div_lt_one hn).mpr hlen
    nlinarith [ht.1]
  have heq : AffineMap.lineMap (radialSegmentCut x y r) y t =
      x+((1-t)*(r/‖y-x‖)+t)•(y-x) := by
    rw [AffineMap.lineMap_apply_module,radialSegmentCut]
    module
  rw [heq,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg ((div_pos hr hn).le.trans hcoef)]
  have hh := mul_le_mul_of_nonneg_right hcoef hn.le
  rwa [div_mul_cancel₀ _ (ne_of_gt hn)] at hh

end
end MatchgateWidth
