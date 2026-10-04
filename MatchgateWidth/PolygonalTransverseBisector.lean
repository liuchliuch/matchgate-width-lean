import MatchgateWidth.PolygonalRibbonGeometry

/-! # Explicit positive transverse directions at polygonal bends -/
namespace MatchgateWidth
noncomputable section

def tangentBisector (a b : ℂ) : ℂ := ‖b‖ • a + ‖a‖ • b

def transverseBisector (a b : ℂ) : ℂ := Complex.I * tangentBisector a b

theorem tangentBisector_norm_sq (a b : ℂ) :
    ‖tangentBisector a b‖^2 = 2*‖a‖*‖b‖*(‖a‖*‖b‖ + a.re*b.re+a.im*b.im) := by
  have ha : a.re^2+a.im^2=‖a‖^2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq a
  have hb : b.re^2+b.im^2=‖b‖^2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq b
  calc
    _ = ‖b‖^2*(a.re^2+a.im^2)+‖a‖^2*(b.re^2+b.im^2)+
      2*‖a‖*‖b‖*(a.re*b.re+a.im*b.im) := by
        rw [← Complex.normSq_eq_norm_sq]
        simp only [tangentBisector, Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.smul_re, Complex.smul_im, smul_eq_mul]
        ring
    _ = _ := by rw [ha,hb]; ring

theorem orientedArea_transverseBisector_left (a b : ℂ) :
    orientedArea a (transverseBisector a b) =
      ‖a‖*(‖a‖*‖b‖+a.re*b.re+a.im*b.im) := by
  have ha : a.re^2+a.im^2=‖a‖^2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq a
  calc
    _ = ‖b‖*(a.re^2+a.im^2)+‖a‖*(a.re*b.re+a.im*b.im) := by
      simp [orientedArea, transverseBisector, tangentBisector, Complex.mul_re,
        Complex.mul_im,  ]
      ring
    _ = _ := by rw [ha]; ring

theorem orientedArea_transverseBisector_right (a b : ℂ) :
    orientedArea b (transverseBisector a b) =
      ‖b‖*(‖a‖*‖b‖+a.re*b.re+a.im*b.im) := by
  have hb : b.re^2+b.im^2=‖b‖^2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq b
  calc
    _ = ‖a‖*(b.re^2+b.im^2)+‖b‖*(a.re*b.re+a.im*b.im) := by
      simp [orientedArea, transverseBisector, tangentBisector, Complex.mul_re,
        Complex.mul_im,  ]
      ring
    _ = _ := by rw [hb]; ring

/-- No strict Cauchy-Schwarz or smoothness hypothesis is needed: a nonzero
weighted tangent sum gives an explicit positive transverse direction for both. -/
theorem transverseBisector_positive {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hbis : tangentBisector a b ≠ 0) :
    0 < orientedArea a (transverseBisector a b) ∧
    0 < orientedArea b (transverseBisector a b) := by
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hpos : 0 < ‖tangentBisector a b‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hbis)
  rw [tangentBisector_norm_sq] at hpos
  have hc : 0 < ‖a‖*‖b‖+a.re*b.re+a.im*b.im :=
    (mul_pos_iff_of_pos_left (by positivity : 0 < 2*‖a‖*‖b‖)).mp hpos
  rw [orientedArea_transverseBisector_left, orientedArea_transverseBisector_right]
  exact ⟨mul_pos han hc,mul_pos hbn hc⟩

end
end MatchgateWidth
