import MatchgateWidth.PolygonalRibbonGeometry

/-! # Radial connectors to polygonal ribbon cross-sections

A cap runs radially from a fraction of a lane endpoint's radius to that actual
endpoint. Exact oriented-area formulas put its interior strictly on the inner
side of the endpoint section. Consequently it can meet the adjoining ribbon
only at its own matching lane endpoint. This does not identify circular ports
with tangent-section points.
-/
namespace MatchgateWidth
noncomputable section

/-- Radial cap from an inner point on the endpoint ray to the actual affine
cross-section endpoint `p + δ • w`, around center `c`. -/
def radialSectionCap (c p w : ℂ) (δ α : ℝ) : unitInterval → ℂ :=
  straightArc (c + α • (ribbonSection p w δ - c)) (ribbonSection p w δ)

@[simp] theorem radialSectionCap_zero (c p w : ℂ) (δ α : ℝ) :
    radialSectionCap c p w δ α 0 = c + α • (ribbonSection p w δ - c) := straightArc_zero _ _
@[simp] theorem radialSectionCap_one (c p w : ℂ) (δ α : ℝ) :
    radialSectionCap c p w δ α 1 = ribbonSection p w δ := straightArc_one _ _

theorem continuous_radialSectionCap (c p w : ℂ) (δ α : ℝ) :
    Continuous (radialSectionCap c p w δ α) := continuous_straightArc _ _

/-- The cap follows exactly one ray, with an increasing affine radial factor. -/
theorem radialSectionCap_sub_center (c p w : ℂ) (δ α : ℝ) (t : unitInterval) :
    radialSectionCap c p w δ α t - c =
      ((1 - (t : ℝ))*α + (t : ℝ)) • (ribbonSection p w δ - c) := by
  apply Complex.ext <;> simp [radialSectionCap, straightArc, ribbonSection] <;> ring

/-- The cap's side of the endpoint cross-section is determined by its original
radial direction, independently of the chosen lane offset. -/
theorem radialSectionCap_area (c p w : ℂ) (δ α : ℝ) (t : unitInterval) :
    orientedArea w (radialSectionCap c p w δ α t - p) =
      (1-α) * (1-(t : ℝ)) * orientedArea (p-c) w := by
  simp [orientedArea, radialSectionCap, straightArc, ribbonSection]
  ring

theorem radialSectionCap_dist (c p w : ℂ) (δ α : ℝ) (hα : 0 ≤ α) (t : unitInterval) :
    dist (radialSectionCap c p w δ α t) c =
      ((1-(t : ℝ))*α+(t : ℝ)) * dist (ribbonSection p w δ) c := by
  rw [dist_eq_norm,radialSectionCap_sub_center,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) hα) t.property.1),dist_eq_norm]

/-- A nondegenerate radial cap is an actual simple arc. -/
theorem radialSectionCap_injective (c p w : ℂ) (δ α : ℝ) (hα : α < 1)
    (hpoint : ribbonSection p w δ ≠ c) :
    Function.Injective (radialSectionCap c p w δ α) := by
  apply straightArc_injective
  intro h
  have hs : α • (ribbonSection p w δ - c) = (1 : ℝ) • (ribbonSection p w δ - c) := by
    simpa only [one_smul,eq_sub_iff_add_eq,add_comm] using h
  have hαeq : α = 1 := smul_left_injective ℝ (sub_ne_zero.mpr hpoint) hs
  exact (ne_of_lt hα) hαeq

/-- Positive radial transversality forces every shifted endpoint away from
the center, without requiring its radius to equal the original cut radius. -/
theorem ribbonSection_ne_center (c p w : ℂ) (δ : ℝ)
    (h : 0 < orientedArea (p-c) w) : ribbonSection p w δ ≠ c := by
  intro he
  have ha : orientedArea (ribbonSection p w δ - c) w = orientedArea (p-c) w := by
    simp [orientedArea,ribbonSection]
    ring
  rw [he,sub_self,orientedArea_zero_left] at ha
  linarith

/-- The complete radial cap stays between its inner and outer radii. -/
theorem radialSectionCap_radius_bounds (c p w : ℂ) (δ α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (t : unitInterval) :
    α * dist (ribbonSection p w δ) c ≤ dist (radialSectionCap c p w δ α t) c ∧
      dist (radialSectionCap c p w δ α t) c ≤ dist (ribbonSection p w δ) c := by
  rw [radialSectionCap_dist _ _ _ _ _ hα0]
  constructor
  · apply mul_le_mul_of_nonneg_right _ dist_nonneg
    nlinarith [t.property.1,t.property.2]
  · have h := mul_le_mul_of_nonneg_right
      (show (1-(t : ℝ))*α+(t : ℝ) ≤ 1 by nlinarith [t.property.1,t.property.2])
      (show 0 ≤ dist (ribbonSection p w δ) c from dist_nonneg)
    simpa only [one_mul] using h

/-- The start cap and the first ribbon segment meet exactly at the matching
lane endpoint. All cap interiors lie on the opposite side of the section. -/
theorem radialSectionCap_ribbon_eq_iff (c p q w v : ℂ) (δ η α : ℝ)
    (hα : α < 1) (hcap : 0 < orientedArea (p-c) w)
    (hwire : 0 < orientedArea (ribbonDirection p q w v η) w)
    (s t : unitInterval) :
    radialSectionCap c p w δ α s = ribbonArc p q w v η t ↔
      s = 1 ∧ t = 0 ∧ δ = η := by
  constructor
  · intro h
    have he := congrArg (fun z => orientedArea w (z-p)) h
    rw [radialSectionCap_area,ribbonArc_after_area] at he
    have hmul : 0 < (1-α)*orientedArea (p-c) w := mul_pos (sub_pos.mpr hα) hcap
    have hnn : 0 ≤ (1-α)*(1-(s : ℝ))*orientedArea (p-c) w :=
      mul_nonneg (mul_nonneg (sub_pos.mpr hα).le (sub_nonneg.mpr s.property.2)) hcap.le
    have ht0 : (t : ℝ) = 0 := by nlinarith [t.property.1]
    have hs1 : (s : ℝ) = 1 := by rw [ht0] at he; nlinarith
    have hs : s = 1 := Subtype.ext hs1
    have ht : t = 0 := Subtype.ext ht0
    subst s
    subst t
    simp only [radialSectionCap_one,ribbonArc_zero,ribbonSection,add_right_inj] at h
    have hw : w ≠ 0 := by intro hz; simp [hz] at hcap
    exact ⟨rfl,rfl,smul_left_injective ℝ hw h⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

/-- At the other endpoint the radial direction is opposite the forward
polygon tangent. Reversing this cap therefore attaches after the last wire
segment, again only at the correct lane endpoint. -/
theorem ribbon_radialSectionCap_eq_iff (c p q u v : ℂ) (δ η α : ℝ)
    (hα : α < 1) (hcap : 0 < orientedArea (c-q) v)
    (hwire : 0 < orientedArea (ribbonDirection p q u v δ) v)
    (s t : unitInterval) :
    ribbonArc p q u v δ s = radialSectionCap c q v η α t ↔
      s = 1 ∧ t = 1 ∧ δ = η := by
  constructor
  · intro h
    have he := congrArg (fun z => orientedArea v (z-q)) h
    rw [ribbonArc_before_area,radialSectionCap_area] at he
    have ha : orientedArea (q-c) v = -orientedArea (c-q) v := by simp [orientedArea]; ring
    rw [ha] at he
    have hmul : 0 < (1-α)*orientedArea (c-q) v := mul_pos (sub_pos.mpr hα) hcap
    have hnn : 0 ≤ (1-(s : ℝ))*orientedArea (ribbonDirection p q u v δ) v :=
      mul_nonneg (sub_nonneg.mpr s.property.2) hwire.le
    have ht1 : (t : ℝ) = 1 := by nlinarith [t.property.1,t.property.2]
    have hs1 : (s : ℝ) = 1 := by rw [ht1] at he; nlinarith
    have hs : s = 1 := Subtype.ext hs1
    have ht : t = 1 := Subtype.ext ht1
    subst s
    subst t
    simp only [radialSectionCap_one,ribbonArc_one,ribbonSection,add_right_inj] at h
    have hv : v ≠ 0 := by intro hz; simp [hz] at hcap
    exact ⟨rfl,rfl,smul_left_injective ℝ hv h⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

/-- Bundled version of the radial connector for use in actual graph gluing. -/
def radialSectionCapPath (c p w : ℂ) (δ α : ℝ) :
    Path (c + α • (ribbonSection p w δ - c)) (ribbonSection p w δ) where
  toFun := radialSectionCap c p w δ α
  continuous_toFun := continuous_radialSectionCap _ _ _ _ _
  source' := radialSectionCap_zero _ _ _ _ _
  target' := radialSectionCap_one _ _ _ _ _

/-- Parameter-free cap-side identity, reusable for the variable-radius
annular connector's final radial portion. -/
theorem radialSection_point_area (c p w : ℂ) (δ β : ℝ) :
    orientedArea w (c + β • (ribbonSection p w δ - c) - p) =
      (1-β) * orientedArea (p-c) w := by
  simp [orientedArea,ribbonSection]
  ring

/-- Euclidean bound for the oriented-area functional. -/
theorem orientedArea_abs_le (a b : ℂ) : |orientedArea a b| ≤ ‖a‖ * ‖b‖ := by
  have he : orientedArea a b = (star a * b).im := by
    simp [orientedArea,Complex.mul_im]
    ring
  rw [he]
  exact (Complex.abs_im_le_norm _).trans_eq (by simp [])

/-- A sufficiently small inner disk is strictly on the inner side of a
transverse endpoint section. Thus the angular-interpolation portion of a
local connector can be separated from its adjoining ribbon too. -/
theorem exists_inner_ball_before_section (c p w : ℂ)
    (h : 0 < orientedArea (p-c) w) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, dist z c ≤ r → 0 < orientedArea w (z-p) := by
  have hw : w ≠ 0 := by intro hz; simp [hz] at h
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let r := orientedArea (p-c) w / (2*‖w‖)
  have hr : 0 < r := div_pos h (by positivity)
  refine ⟨r,hr,?_⟩
  intro z hz
  have he : orientedArea w (z-p) = orientedArea w (z-c) + orientedArea (p-c) w := by
    simp [orientedArea]
    ring
  have hb := (abs_le.mp (orientedArea_abs_le w (z-c))).1
  have hm := mul_le_mul_of_nonneg_left hz hn.le
  rw [dist_eq_norm] at hm
  have hrr : ‖w‖ * r = orientedArea (p-c) w / 2 := by
    dsimp [r]
    field_simp
  rw [hrr] at hm
  rw [he]
  linarith

end
end MatchgateWidth
