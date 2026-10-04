import MatchgateWidth.PlanarDrawing

/-! Elementary straight-arc helpers for explicit scaled-square disk drawings. -/

namespace MatchgateWidth

noncomputable section

/-- A straight arc parameterized by the closed unit interval. -/
def straightArc (p q : ℂ) (t : unitInterval) : ℂ :=
  (1 - (t : ℝ)) • p + (t : ℝ) • q

@[simp] theorem straightArc_zero (p q : ℂ) : straightArc p q 0 = p := by
  simp [straightArc]

@[simp] theorem straightArc_one (p q : ℂ) : straightArc p q 1 = q := by
  simp [straightArc]

theorem continuous_straightArc (p q : ℂ) : Continuous (straightArc p q) := by
  unfold straightArc
  fun_prop

theorem straightArc_injective {p q : ℂ} (hpq : p ≠ q) :
    Function.Injective (straightArc p q) := by
  intro t u h
  have hh : ((t : ℝ) - (u : ℝ)) • (q - p) = 0 := by
    calc
      _ = straightArc p q t - straightArc p q u := by
        simp only [straightArc, sub_smul, smul_sub, one_smul]
        abel
      _ = 0 := sub_eq_zero.mpr h
  rcases smul_eq_zero.mp hh with ht | hp
  · exact Subtype.ext (sub_eq_zero.mp ht)
  · exact (hpq (sub_eq_zero.mp hp).symm).elim

theorem straightArc_in_disk {p q : ℂ} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (t : unitInterval) : ‖straightArc p q t‖ ≤ 1 := by
  have hp' : p ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hp
  have hq' : q ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hq
  have h := convex_closedBall (0 : ℂ) 1 hp' hq'
    (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  simpa [straightArc] using h

/-- The side-coordinate scale of an inscribed square. -/
def squareScale : ℝ := Real.sqrt 2 / 2

theorem squareScale_pos : 0 < squareScale := by unfold squareScale; positivity

theorem squareScale_sq : squareScale ^ 2 = 1 / 2 := by
  unfold squareScale
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Cartesian coordinates scaled to an inscribed square. -/
def squarePoint (x y : ℝ) : ℂ := ⟨squareScale * x, squareScale * y⟩

@[simp] theorem squarePoint_inj (a b c d : ℝ) :
    squarePoint a b = squarePoint c d ↔ a = c ∧ b = d := by
  simp only [Complex.ext_iff, squarePoint, mul_right_inj' (ne_of_gt squareScale_pos)]

theorem squarePoint_in_disk {x y : ℝ} (h : x * x + y * y ≤ 2) :
    ‖squarePoint x y‖ ≤ 1 := by
  have hs := squareScale_sq
  have h' : ‖squarePoint x y‖ ^ 2 = squareScale ^ 2 * (x*x+y*y) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change (squareScale * x) * (squareScale * x) +
      (squareScale * y) * (squareScale * y) = _
    ring
  rw [hs] at h'
  nlinarith [norm_nonneg (squarePoint x y)]

@[simp] theorem straightArc_squarePoint (a b c d : ℝ) (t : unitInterval) :
    straightArc (squarePoint a b) (squarePoint c d) t =
      squarePoint ((1 - (t : ℝ)) * a + (t : ℝ) * c)
        ((1 - (t : ℝ)) * b + (t : ℝ) * d) := by
  apply Complex.ext <;> simp [straightArc, squarePoint] <;> ring

@[simp] theorem boundaryPoint_re (a : ℝ) :
    (boundaryPoint a).re = Real.cos (2 * Real.pi * a) := by
  unfold boundaryPoint circleMap
  simp only [Complex.ofReal_one, one_mul, zero_add]
  exact Complex.exp_ofReal_mul_I_re _

@[simp] theorem boundaryPoint_im (a : ℝ) :
    (boundaryPoint a).im = Real.sin (2 * Real.pi * a) := by
  unfold boundaryPoint circleMap
  simp only [Complex.ofReal_one, one_mul, zero_add]
  exact Complex.exp_ofReal_mul_I_im _

/-- The first square corner has angular coordinate one eighth of a turn. -/
theorem squarePoint_one_one : squarePoint 1 1 = boundaryPoint (1/8) := by
  have h : 2 * Real.pi * (1 / 8 : ℝ) = Real.pi / 4 := by ring
  apply Complex.ext <;>
    simp only [boundaryPoint_re, boundaryPoint_im, h, Real.cos_pi_div_four,
      Real.sin_pi_div_four, squarePoint, squareScale, mul_one]

theorem squarePoint_neg_one_one : squarePoint (-1) 1 = boundaryPoint (3/8) := by
  have h : 2 * Real.pi * (3 / 8 : ℝ) = Real.pi - Real.pi / 4 := by ring
  apply Complex.ext <;>
    simp only [boundaryPoint_re, boundaryPoint_im, h, Real.cos_pi_sub,
      Real.sin_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four,
      squarePoint, squareScale, mul_one, mul_neg_one]

theorem squarePoint_neg_one_neg_one : squarePoint (-1) (-1) = boundaryPoint (5/8) := by
  have h : 2 * Real.pi * (5 / 8 : ℝ) = Real.pi / 4 + Real.pi := by ring
  apply Complex.ext <;>
    simp only [boundaryPoint_re, boundaryPoint_im, h, Real.cos_add_pi,
      Real.sin_add_pi, Real.cos_pi_div_four, Real.sin_pi_div_four,
      squarePoint, squareScale, mul_neg_one]

theorem squarePoint_one_neg_one : squarePoint 1 (-1) = boundaryPoint (7/8) := by
  have h : 2 * Real.pi * (7 / 8 : ℝ) = 2 * Real.pi - Real.pi / 4 := by ring
  apply Complex.ext <;>
    simp only [boundaryPoint_re, boundaryPoint_im, h, Real.cos_two_pi_sub,
      Real.sin_two_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four,
      squarePoint, squareScale, mul_one, mul_neg_one]

/-- Counterclockwise corners, starting at the upper right. -/
def squareCorners : Fin 4 → ℂ :=
  ![squarePoint 1 1, squarePoint (-1) 1, squarePoint (-1) (-1), squarePoint 1 (-1)]

def squareAngles : Fin 4 → ℝ := ![1/8, 3/8, 5/8, 7/8]

theorem squareCorners_injective : Function.Injective squareCorners := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [squareCorners] at *

theorem squareCorners_in_disk (i : Fin 4) : ‖squareCorners i‖ ≤ 1 := by
  fin_cases i <;> apply squarePoint_in_disk <;> norm_num

theorem squareAngles_pos (i : Fin 4) : 0 < squareAngles i := by
  fin_cases i <;> norm_num [squareAngles]

theorem squareAngles_lt_one (i : Fin 4) : squareAngles i < 1 := by
  fin_cases i <;> norm_num [squareAngles]

theorem squareAngles_strictMono : StrictMono squareAngles := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [squareAngles] at *

theorem squareCorners_boundary (i : Fin 4) : squareCorners i = boundaryPoint (squareAngles i) := by
  fin_cases i
  · exact squarePoint_one_one
  · exact squarePoint_neg_one_one
  · exact squarePoint_neg_one_neg_one
  · exact squarePoint_one_neg_one

end
end MatchgateWidth
