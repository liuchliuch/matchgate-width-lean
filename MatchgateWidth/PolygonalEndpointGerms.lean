import MatchgateWidth.PolygonalPathRealization

/-! # Straight endpoint germs of genuine finite polygonal paths -/
namespace MatchgateWidth
noncomputable section
open Set unitInterval

/-- Reversing a finite polygonal path preserves finite polygonality. -/
theorem IsPolygonalPath.symm {x y : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) : IsPolygonalPath p.symm := by
  induction hp with
  | segment x y => simpa using IsPolygonalPath.segment y x
  | trans hp hq ihp ihq => simpa using IsPolygonalPath.trans ihq ihp

/-- Every finite polygonal path has a constant-velocity initial germ, possibly
stationary when the original path is not injective. -/
theorem IsPolygonalPath.exists_source_germ {x y : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) :
    ∃ τ : unitInterval, 0 < τ ∧ ∃ v : ℂ,
      ∀ t : unitInterval, t ≤ τ → p t = x + (t : ℝ) • v := by
  induction hp with
  | segment x y =>
    refine ⟨1, zero_lt_one, y-x, ?_⟩
    intro t ht
    simp only [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  | @trans x y z p q hp hq ihp ihq =>
    obtain ⟨τ,hτ,v,hv⟩ := ihp
    let δ : unitInterval := ⟨(τ : ℝ)/2, by constructor <;> linarith [τ.2.1,τ.2.2]⟩
    refine ⟨δ, ?_, (2 : ℝ) • v, ?_⟩
    · change 0 < (τ : ℝ)/2
      exact div_pos hτ zero_lt_two
    · intro t ht
      have ht' : (t : ℝ) ≤ (τ : ℝ)/2 := ht
      have hhalf : (t : ℝ) ≤ 1/2 := by linarith [τ.2.2]
      rw [Path.trans_apply, dite_eq_left hhalf, hv]
      · simp only [smul_smul]
        congr 1
        congr 1
        ring
      · change 2 * (t : ℝ) ≤ τ
        linarith

/-- Injectivity rules out a stationary first segment. -/
theorem IsPolygonalPath.exists_nonzero_source_germ {x y : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) (hi : Function.Injective p) :
    ∃ τ : unitInterval, 0 < τ ∧ ∃ v : ℂ, v ≠ 0 ∧
      ∀ t : unitInterval, t ≤ τ → p t = x + (t : ℝ) • v := by
  obtain ⟨τ,hτ,v,hv⟩ := hp.exists_source_germ
  refine ⟨τ,hτ,v,?_,hv⟩
  intro hv0
  have heq : p τ = p 0 := by simpa [hv0] using hv τ le_rfl
  exact (ne_of_gt hτ) (hi heq)

/-- At the target, positive time is measured backwards from the endpoint. -/
theorem IsPolygonalPath.exists_nonzero_target_germ {x y : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) (hi : Function.Injective p) :
    ∃ τ : unitInterval, 0 < τ ∧ ∃ v : ℂ, v ≠ 0 ∧
      ∀ t : unitInterval, t ≤ τ → p.symm t = y + (t : ℝ) • v := by
  exact hp.symm.exists_nonzero_source_germ (hi.comp unitInterval.symm_involutive.injective)

/-- A nonzero straight germ lying on a radial segment has positive radial
velocity; containment in a ray cannot reverse the endpoint direction. -/
theorem positive_smul_of_mem_radial_segment {x v V : ℂ} {t : ℝ}
    (ht : 0 < t) (hv : v ≠ 0)
    (hz : x + t • v ∈ _root_.segment ℝ x (x+V)) :
    ∃ κ : ℝ, 0 < κ ∧ v = κ • V := by
  obtain ⟨u,hu,heq⟩ := (show x + t • v ∈
      AffineMap.lineMap x (x+V) '' Icc (0 : ℝ) 1 by
    simpa only [← segment_eq_image_lineMap] using hz)
  have heq' : u • V = t • v := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at heq
    linear_combination (norm := module) heq
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0,zero_smul] at heq'
    exact (smul_ne_zero (ne_of_gt ht) hv) heq'.symm
  refine ⟨u/t,div_pos (lt_of_le_of_ne hu.1 hu0.symm) ht,?_⟩
  calc
    v = t⁻¹ • (t • v) := (inv_smul_smul₀ (ne_of_gt ht) v).symm
    _ = t⁻¹ • (u • V) := by rw [heq']
    _ = (u/t) • V := by rw [smul_smul]; congr 1; field_simp

/-- Metric-local containment in an original radial segment preserves the
endpoint direction up to a strictly positive speed change. -/
theorem IsPolygonalPath.exists_positive_source_germ {x y V : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) (hi : Function.Injective p)
    (hloc : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.range p,
      dist z x < ε → z ∈ _root_.segment ℝ x (x+V)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ τ : unitInterval, 0 < τ ∧
      ∀ t : unitInterval, t ≤ τ → p t = x + (t : ℝ) • (κ • V) := by
  obtain ⟨τ,hτ,v,hv,hgerm⟩ := hp.exists_nonzero_source_germ hi
  obtain ⟨ε,hε,hloc⟩ := hloc
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r : ℝ := min (τ : ℝ) (ε / (2 * ‖v‖))
  have hrpos : 0 < r := lt_min hτ (div_pos hε (mul_pos zero_lt_two hvnorm))
  have hrτ : r ≤ (τ : ℝ) := min_le_left _ _
  have hrε : r ≤ ε / (2 * ‖v‖) := min_le_right _ _
  let u : unitInterval := ⟨r,hrpos.le,hrτ.trans τ.2.2⟩
  have huτ : u ≤ τ := hrτ
  have hdist : dist (p u) x < ε := by
    rw [hgerm u huτ, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    change |r| * ‖v‖ < ε
    rw [abs_of_pos hrpos]
    have hmul : r * (2 * ‖v‖) ≤ ε := (le_div_iff₀ (mul_pos zero_lt_two hvnorm)).mp hrε
    nlinarith
  have hmem := hloc (p u) ⟨u,rfl⟩ hdist
  rw [hgerm u huτ] at hmem
  obtain ⟨κ,hκ,hvκ⟩ := positive_smul_of_mem_radial_segment hrpos hv hmem
  exact ⟨κ,hκ,τ,hτ,fun t ht => by rw [hgerm t ht,hvκ]⟩

/-- Target version of radial endpoint-germ preservation. -/
theorem IsPolygonalPath.exists_positive_target_germ {x y V : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) (hi : Function.Injective p)
    (hloc : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.range p,
      dist z y < ε → z ∈ _root_.segment ℝ y (y+V)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ τ : unitInterval, 0 < τ ∧
      ∀ t : unitInterval, t ≤ τ → p.symm t = y + (t : ℝ) • (κ • V) := by
  apply hp.symm.exists_positive_source_germ (hi.comp unitInterval.symm_involutive.injective)
  simpa only [Path.symm_range] using hloc

/-- The velocity of a nontrivial straight endpoint germ is unique. Neither
polygonality nor injectivity is needed once both germ identities are known. -/
theorem source_germ_velocity_unique {p : unitInterval → ℂ} {x v w : ℂ}
    {τ ρ : unitInterval} (hτ : 0 < τ) (hρ : 0 < ρ)
    (hv : ∀ t : unitInterval, t ≤ τ → p t = x + (t : ℝ) • v)
    (hw : ∀ t : unitInterval, t ≤ ρ → p t = x + (t : ℝ) • w) : v = w := by
  have ht : 0 < min τ ρ := lt_min hτ hρ
  have heq : x + ((min τ ρ : unitInterval) : ℝ) • v =
      x + ((min τ ρ : unitInterval) : ℝ) • w :=
    (hv (min τ ρ) (min_le_left _ _)).symm.trans
      (hw (min τ ρ) (min_le_right _ _))
  exact smul_right_injective ℂ (ne_of_gt ht) (add_left_cancel heq)

end
end MatchgateWidth
