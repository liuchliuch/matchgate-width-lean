import MatchgateWidth.SquareRayAngles
import MatchgateWidth.PolygonalRibbonGeometry

/-! # Transverse endpoint offsets preserve the actual local port order

Angles are calculated from the endpoints themselves in a common fixed frame.
A finite neighbourhood controls every inter-sector gap simultaneously, while
positive transverse area supplies strict within-sector order.
-/
namespace MatchgateWidth
noncomputable section
open Filter Topology

/-- The change of angle, in turns, of `p + δ • w` relative to `p`. -/
def transverseAngleChange (p w : ℂ) (δ : ℝ) : ℝ :=
  Real.arctan (δ*(w/p).im/(1+δ*(w/p).re))/(2*Real.pi)

/-- The accompanying positive radial scale in the right-half-plane chart. -/
def transverseRadiusFactor (p w : ℂ) (δ : ℝ) : ℝ :=
  (1+δ*(w/p).re) *
    (Real.cos (Real.arctan (δ*(w/p).im/(1+δ*(w/p).re))))⁻¹

@[simp] theorem transverseAngleChange_zero (p w : ℂ) :
    transverseAngleChange p w 0 = 0 := by simp [transverseAngleChange]

@[simp] theorem transverseRadiusFactor_zero (p w : ℂ) :
    transverseRadiusFactor p w 0 = 1 := by simp [transverseRadiusFactor]

theorem transverseAngleChange_continuousAt_zero (p w : ℂ) :
    ContinuousAt (transverseAngleChange p w) 0 := by
  unfold transverseAngleChange
  fun_prop (disch := norm_num)

theorem transverseRadiusFactor_pos {p w : ℂ} {δ : ℝ}
    (h : 0 < 1+δ*(w/p).re) : 0 < transverseRadiusFactor p w δ :=
  mul_pos h (inv_pos.mpr (Real.cos_arctan_pos _))

theorem im_div_pos_of_orientedArea {p w : ℂ} (h : 0 < orientedArea p w) :
    0 < (w/p).im := by
  have hp : p ≠ 0 := by intro hp; simp [hp] at h
  rw [Complex.div_im, ← sub_div]
  apply div_pos _ (Complex.normSq_pos.mpr hp)
  simpa only [orientedArea, mul_comm] using h

/-- Actual angular monotonicity along a positively transverse affine cap. -/
theorem transverseAngleChange_strictMonoOn {p w : ℂ}
    (h : 0 < orientedArea p w) :
    StrictMonoOn (transverseAngleChange p w) {δ | 0 < 1+δ*(w/p).re} := by
  intro δ hδ η hη hδη
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2*Real.pi)).mpr
  apply Real.arctan_strictMono
  apply (div_lt_div_iff₀ hδ hη).mpr
  have hp := im_div_pos_of_orientedArea h
  nlinarith

/-- The sign-sensitive version also covers incoming caps, whose lane order is
reversed because their transverse area relative to the outward ray is negative. -/
theorem transverseAngleChange_lt_of_signed_area {p w : ℂ} {δ η : ℝ}
    (hδ : 0 < 1+δ*(w/p).re) (hη : 0 < 1+η*(w/p).re)
    (harea : 0 < (η-δ)*orientedArea p w) :
    transverseAngleChange p w δ < transverseAngleChange p w η := by
  have hp : p ≠ 0 := by intro hp; simp [hp] at harea
  have him : 0 < (η-δ)*(w/p).im := by
    have he : (η-δ)*(w/p).im = ((η-δ)*orientedArea p w)/Complex.normSq p := by
      rw [Complex.div_im]
      unfold orientedArea
      ring
    rw [he]
    exact div_pos harea (Complex.normSq_pos.mpr hp)
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2*Real.pi)).mpr
  apply Real.arctan_strictMono
  apply (div_lt_div_iff₀ hδ hη).mpr
  nlinarith

private theorem inv_cos_mul_sin_arctan' (x : ℝ) :
    (Real.cos (Real.arctan x))⁻¹ * Real.sin (Real.arctan x) = x := by
  rw [Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1+x^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

/-- Exact factorization of a perturbed complex vector. -/
theorem transversePoint_eq {p w : ℂ} (hp : p ≠ 0) {δ : ℝ}
    (hδ : 0 < 1+δ*(w/p).re) :
    p + (δ:ℂ)*w = p * (transverseRadiusFactor p w δ : ℂ) *
      boundaryPoint (transverseAngleChange p w δ) := by
  have hphase : 2*Real.pi*transverseAngleChange p w δ =
      Real.arctan (δ*(w/p).im/(1+δ*(w/p).re)) := by
    unfold transverseAngleChange; field_simp
  have hcos (x : ℝ) : (Real.cos (Real.arctan x))⁻¹ * Real.cos (Real.arctan x) = 1 :=
    inv_mul_cancel₀ (ne_of_gt (Real.cos_arctan_pos x))
  have hlocal : (1:ℂ)+(δ:ℂ)*(w/p) = (transverseRadiusFactor p w δ : ℂ) *
      boundaryPoint (transverseAngleChange p w δ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, boundaryPoint_re, hphase]
      unfold transverseRadiusFactor
      rw [mul_assoc, hcos, mul_one]
    · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_add, boundaryPoint_im, hphase]
      unfold transverseRadiusFactor
      rw [mul_assoc, inv_cos_mul_sin_arctan', mul_div_cancel₀ _ (ne_of_gt hδ)]
  calc
    _ = p * ((1:ℂ)+(δ:ℂ)*(w/p)) := by field_simp
    _ = _ := by rw [hlocal, mul_assoc]

theorem boundaryPoint_mul (a b : ℝ) :
    boundaryPoint a * boundaryPoint b = boundaryPoint (a+b) := by
  unfold boundaryPoint
  rw [circleMap_zero_mul, one_mul]
  congr 1
  ring

/-- The standard `Fin (n*r)` layout is port-major and lane-minor. -/
theorem strictMono_flatten_blocks {n r : ℕ} (f : Fin n → Fin r → ℝ)
    (hwithin : ∀ i, StrictMono (f i))
    (hbetween : ∀ i j k l, i < j → f i k < f j l) :
    StrictMono (fun x : Fin (n*r) =>
      f (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2) := by
  intro a b hab
  simp only [finProdFinEquiv_symm_apply]
  have hd : a.divNat ≤ b.divNat := by
    change a.val/r ≤ b.val/r
    exact Nat.div_le_div_right (Fin.le_iff_val_le_val.mp hab.le)
  by_cases he : a.divNat = b.divNat
  · have hm : a.modNat < b.modNat := by
      have he' : a.val/r = b.val/r := congrArg Fin.val he
      change a.val%r < b.val%r
      have ha := Nat.mod_add_div a.val r
      have hb := Nat.mod_add_div b.val r
      rw [he'] at ha
      have hab' : a.val < b.val := hab
      omega
    rw [he]
    exact hwithin _ hm
  · exact hbetween _ _ _ _ (lt_of_le_of_ne hd he)

namespace OrderedRayAngles

variable {n : ℕ} {p : Fin n → ℂ} (A : OrderedRayAngles p)

/-- The actual angles in the same local frame after endpoint perturbation. -/
def perturbedAngle (w : Fin n → ℂ) (δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  A.angle i + transverseAngleChange (p i) (w i) (δ i)

/-- Every finite family of actual offset endpoints has the calculated angular
coordinates, with the original frame unchanged. -/
theorem perturbed_point_eq (w : Fin n → ℂ) (δ : Fin n → ℝ)
    (hδ : ∀ i, 0 < 1+δ i*(w i/p i).re) (i : Fin n) :
    p i + (δ i:ℂ)*w i = A.rotation *
      ((A.radius i * transverseRadiusFactor (p i) (w i) (δ i) : ℝ):ℂ) *
      boundaryPoint (A.perturbedAngle w δ i) := by
  have hp : p i ≠ 0 := by
    rw [A.point_eq]
    exact mul_ne_zero (mul_ne_zero A.rotation_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (A.radius_pos i))))
      (by intro he; have hn := congrArg norm he; simp at hn)
  unfold perturbedAngle
  rw [transversePoint_eq hp (hδ i), A.point_eq i]
  rw [← boundaryPoint_mul, Complex.ofReal_mul]
  ring

/-- One global ribbon width, with an arbitrary finite family of lane offsets. -/
def blockAngle {r : ℕ} (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (ε : ℝ) (i : Fin n) (k : Fin r) : ℝ :=
  A.angle i + transverseAngleChange (p i) (w i) (ε*d i k)

@[simp] theorem blockAngle_zero {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (i : Fin n) (k : Fin r) :
    A.blockAngle w d 0 i k = A.angle i := by simp [blockAngle]

theorem blockAngle_continuousAt_zero {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (i : Fin n) (k : Fin r) :
    ContinuousAt (fun ε => A.blockAngle w d ε i k) 0 := by
  unfold blockAngle transverseAngleChange
  fun_prop (disch := norm_num)

/-- All finite inter-sector gaps and the common cut survive simultaneously.
The conclusion is computed from the actual endpoint angles. -/
theorem eventually_blockAngle_order {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) :
    ∀ᶠ ε in 𝓝 (0:ℝ),
      (∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re) ∧
      (∀ i k, 0 < A.blockAngle w d ε i k ∧ A.blockAngle w d ε i k < 1) ∧
      (∀ i j k l, i < j → A.blockAngle w d ε i k < A.blockAngle w d ε j l) := by
  have hden : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro k
    apply continuousAt_const.eventually_lt
      (show ContinuousAt (fun ε : ℝ => 1+(ε*d i k)*(w i/p i).re) 0 by fun_prop)
    norm_num
  have hrange : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ i k,
      0 < A.blockAngle w d ε i k ∧ A.blockAngle w d ε i k < 1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro k
    exact (continuousAt_const.eventually_lt (A.blockAngle_continuousAt_zero w d i k)
      (by simpa using A.angle_pos i)).and
      ((A.blockAngle_continuousAt_zero w d i k).eventually_lt continuousAt_const
        (by simpa using A.angle_lt_one i))
  have hbetween : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ i j k l,
      i < j → A.blockAngle w d ε i k < A.blockAngle w d ε j l := by
    simp only [Filter.eventually_all]
    intro i j k l hij
    exact (A.blockAngle_continuousAt_zero w d i k).eventually_lt
      (A.blockAngle_continuousAt_zero w d j l) (by simpa using A.angle_strictMono hij)
  exact hden.and (hrange.and hbetween)

/-- Positively transverse offsets are strictly ordered within each sector. -/
theorem blockAngle_strictMono {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (harea : ∀ i, 0 < orientedArea (p i) (w i))
    (hd : ∀ i, StrictMono (d i)) {ε : ℝ} (hε : 0 < ε)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re) (i : Fin n) :
    StrictMono (A.blockAngle w d ε i) := by
  intro k l hkl
  unfold blockAngle
  apply add_lt_add_right
  exact transverseAngleChange_strictMonoOn (harea i) (hden i k) (hden i l)
    (mul_lt_mul_of_pos_left (hd i hkl) hε)

/-- Within-block monotonicity with either transverse orientation. -/
theorem blockAngle_strictMono_of_signed_area {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ)
    (horder : ∀ i k l, k < l → 0 < (d i l-d i k)*orientedArea (p i) (w i))
    {ε : ℝ} (hε : 0 < ε)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re) (i : Fin n) :
    StrictMono (A.blockAngle w d ε i) := by
  intro k l hkl
  unfold blockAngle
  apply add_lt_add_right
  apply transverseAngleChange_lt_of_signed_area (hden i k) (hden i l)
  have h := mul_pos hε (horder i k l hkl)
  nlinarith

/-- Actual flattened endpoint coordinates, with no change to port/lane labels. -/
def blockEndpoint (_A : OrderedRayAngles p) {r : ℕ} (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (ε : ℝ) (x : Fin (n*r)) : ℂ :=
  let i := (finProdFinEquiv.symm x).1
  let k := (finProdFinEquiv.symm x).2
  p i + ((ε*d i k : ℝ):ℂ)*w i

/-- For every sufficiently small positive width, all ribbon cap endpoints admit
actual strictly increasing open-turn angles in the original common frame.
Both the marked first port and every within-block lane index are unchanged. -/
theorem exists_ordered_blockEndpoints_of_signed_area {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ)
    (horder : ∀ i k l, k < l → 0 < (d i l-d i k)*orientedArea (p i) (w i)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : OrderedRayAngles (A.blockEndpoint w d ε), B.rotation = A.rotation := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp (A.eventually_blockAngle_order w d)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεlt
  have hmem : ε ∈ Metric.ball (0:ℝ) ε₀ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε] using hεlt
  obtain ⟨hden, hrange, hbetween⟩ := hball hmem
  refine ⟨{
    rotation := A.rotation
    rotation_ne_zero := A.rotation_ne_zero
    angle := fun x => A.blockAngle w d ε (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2
    angle_strictMono := strictMono_flatten_blocks _
      (A.blockAngle_strictMono_of_signed_area w d horder hε hden) hbetween
    angle_pos := fun x => (hrange _ _).1
    angle_lt_one := fun x => (hrange _ _).2
    radius := fun x => A.radius (finProdFinEquiv.symm x).1 *
      transverseRadiusFactor (p (finProdFinEquiv.symm x).1) (w (finProdFinEquiv.symm x).1)
        (ε*d (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
    radius_pos := fun x => mul_pos (A.radius_pos _)
      (transverseRadiusFactor_pos (hden _ _))
    point_eq := ?_ }, rfl⟩
  intro x
  exact A.perturbed_point_eq w (fun i => ε*d i (finProdFinEquiv.symm x).2)
    (fun i => hden i _) (finProdFinEquiv.symm x).1

/-- Positive-area specialization for outward caps with increasing lane offsets. -/
theorem exists_ordered_blockEndpoints {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (harea : ∀ i, 0 < orientedArea (p i) (w i))
    (hd : ∀ i, StrictMono (d i)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : OrderedRayAngles (A.blockEndpoint w d ε), B.rotation = A.rotation :=
  A.exists_ordered_blockEndpoints_of_signed_area w d
    (fun i _ _ hkl => mul_pos (sub_pos.mpr (hd i hkl)) (harea i))

/-- Negative-area specialization for incoming caps with decreasing offsets. -/
theorem exists_ordered_blockEndpoints_reversed {r : ℕ} (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (harea : ∀ i, orientedArea (p i) (w i) < 0)
    (hd : ∀ i, StrictAnti (d i)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : OrderedRayAngles (A.blockEndpoint w d ε), B.rotation = A.rotation :=
  A.exists_ordered_blockEndpoints_of_signed_area w d
    (fun i _ _ hkl => mul_pos_of_neg_of_neg (sub_neg.mpr (hd i hkl)) (harea i))

end OrderedRayAngles
/-- End-to-end local angular alignment directly from `PositivePortOrder`.
No angular-order certificate is assumed: the common frame and every strictly
ordered list are constructed from the square-ray germ and transverse offsets.
The signed-area condition covers outgoing/increasing and incoming/decreasing
lane offsets in the same statement. -/
theorem positivePortOrder_ordered_transverseEndpoints {n r : ℕ} {vertex : ℂ}
    {arc : Fin n → unitInterval → ℂ}
    (P : LabelledInstance.PositivePortOrder vertex arc)
    (t : Fin n → unitInterval) (ht : ∀ i, 0 < t i) (htP : ∀ i, t i ≤ P.radius)
    (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (horder : ∀ i k l, k < l →
      0 < (d i l-d i k)*orientedArea (arc i (t i)-vertex) (w i)) :
    ∃ rotation : ℂ, rotation ≠ 0 ∧ ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : OrderedRayAngles (fun x : Fin (n*r) =>
        let i := (finProdFinEquiv.symm x).1
        let k := (finProdFinEquiv.symm x).2
        arc i (t i)-vertex + ((ε*d i k : ℝ):ℂ)*w i),
        B.rotation = rotation := by
  obtain ⟨A⟩ := positivePortOrder_germ_orderedRayAngles P t ht htP
  obtain ⟨ε₀, hε₀, hsmall⟩ := A.exists_ordered_blockEndpoints_of_signed_area w d horder
  exact ⟨A.rotation, A.rotation_ne_zero, ε₀, hε₀, hsmall⟩

end
end MatchgateWidth
