import MatchgateWidth.PolygonalDrawingRoutes
import MatchgateWidth.IndexedPolygonalTrimming
import MatchgateWidth.PolygonalEndpointGerms

/-! # Positive tangent agreement for indexed routes in radial path traces -/
namespace MatchgateWidth
noncomputable section
open Set

/-- Simplicity prevents remote portions of a radial path from returning to
its endpoint. Locally, the entire trace therefore lies on its original ray. -/
theorem Path.local_radial_segment {x y v : ℂ} (p : Path x y)
    (hi : Function.Injective p) {τ : unitInterval} (hτ : 0<τ)
    (hg : ∀ t : unitInterval, t≤τ → p t=x+(t:ℝ)•v) :
    ∃ ε : ℝ, 0<ε ∧ ∀ z∈Set.range p, dist z x<ε → z∈segment ℝ x (x+(τ:ℝ)•v) := by
  obtain ⟨ε,hε,hsep⟩ := path_initial_ball_avoids_tail p hi τ hτ
  refine ⟨ε,hε,?_⟩
  rintro z ⟨t,rfl⟩ hd
  have ht : t≤τ := by
    by_contra hn
    exact (not_lt_of_ge (hsep t (le_of_lt (lt_of_not_ge hn)))) hd
  have hτr : 0<(τ:ℝ) := hτ
  have htr : (t:ℝ)≤τ := ht
  refine ⟨1-(t:ℝ)/(τ:ℝ),(t:ℝ)/(τ:ℝ),
    sub_nonneg.mpr ((div_le_one hτr).mpr htr),div_nonneg t.2.1 hτr.le,by ring,?_⟩
  rw [hg t ht]
  calc
    _ = x+(((t:ℝ)/(τ:ℝ))*(τ:ℝ))•v := by module
    _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt hτr)]

/-- Any nondegenerate straight segment in the trace of a simple radial path,
starting at its endpoint, has the same positive radial direction. -/
theorem segment_direction_positive_of_path_germ {x y z v : ℂ} (p : Path x y)
    (hi : Function.Injective p) (hxz : x≠z)
    (hseg : segment ℝ x z ⊆ Set.range p)
    {τ : unitInterval} (hτ : 0<τ)
    (hg : ∀ t : unitInterval, t≤τ → p t=x+(t:ℝ)•v) :
    ∃ κ : ℝ, 0<κ ∧ z-x=κ•v := by
  obtain ⟨ε,hε,hloc⟩ := Path.local_radial_segment p hi hτ hg
  have hqloc : ∃ ε : ℝ, 0<ε ∧ ∀ w∈Set.range (Path.segment x z),
      dist w x<ε → w∈segment ℝ x (x+(τ:ℝ)•v) := by
    refine ⟨ε,hε,?_⟩
    intro w hw hd
    exact hloc w (hseg (by simpa only [Path.range_segment] using hw)) hd
  obtain ⟨κ,hκ,ρ,hρ,hq⟩ := (IsPolygonalPath.segment x z).exists_positive_source_germ
    (Path.segment_injective_of_ne hxz) hqloc
  have hv : z-x=κ•((τ:ℝ)•v) := source_germ_velocity_unique
    (show (0:unitInterval)<1 from zero_lt_one) hρ
    (fun t _ => by
      simp only [Path.segment_apply,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add]
      module) hq
  exact ⟨κ*(τ:ℝ),mul_pos hκ hτ,by simpa only [smul_smul] using hv⟩

namespace IndexedSimplePolygonalRoute

/-- The first indexed segment has positive tangent agreement with the actual
original source germ, not merely trace containment. -/
theorem first_tangent_positive {x y v : ℂ} {p : Path x y}
    (R : IndexedSimplePolygonalRoute (Set.range p) x y)
    (hi : Function.Injective p) {τ : unitInterval} (hτ : 0<τ)
    (hg : ∀ t : unitInterval, t≤τ → p t=x+(t:ℝ)•v) :
    ∃ κ : ℝ, 0<κ ∧ R.vertex R.firstEdge.succ-x=κ•v := by
  apply segment_direction_positive_of_path_germ p hi
  · simpa only [R.firstEdge_castSucc,R.source] using R.nonzero R.firstEdge
  · simpa only [R.firstEdge_castSucc,R.source] using R.segment_subset R.firstEdge
  · exact hτ
  · exact hg

/-- The reversed final segment has positive tangent agreement with the
original outgoing radial germ at the target. -/
theorem last_reverse_tangent_positive {x y v : ℂ} {p : Path x y}
    (R : IndexedSimplePolygonalRoute (Set.range p) x y)
    (hi : Function.Injective p) {τ : unitInterval} (hτ : 0<τ)
    (hg : ∀ t : unitInterval, t≤τ → p.symm t=y+(t:ℝ)•v) :
    ∃ κ : ℝ, 0<κ ∧ R.vertex R.lastEdge.castSucc-y=κ•v := by
  apply segment_direction_positive_of_path_germ p.symm
    (hi.comp unitInterval.symm_involutive.injective)
  · simpa only [R.lastEdge_succ,R.target] using (R.nonzero R.lastEdge).symm
  · rw [Path.symm_range,segment_symm]
    simpa only [R.lastEdge_succ,R.target] using R.segment_subset R.lastEdge
  · exact hτ
  · exact hg

end IndexedSimplePolygonalRoute
end
end MatchgateWidth
