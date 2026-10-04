import MatchgateWidth.LabelledInstances
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Actual angular coordinates for the ordered square rays

The square-perimeter parameter has a strictly increasing real lift of its
angle. The lift, and the positive radial scale, are explicitly calculated.
-/
namespace MatchgateWidth
noncomputable section

/-- Lifted angle in radians; its values on `[0,4)` lie in `[-π/4,7π/4)`. -/
def squareRayAngle (t : ℝ) : ℝ :=
  if t ≤ 1 then Real.arctan (2*t-1)
  else if t ≤ 2 then Real.pi/2 + Real.arctan (2*t-3)
  else if t ≤ 3 then Real.pi + Real.arctan (2*t-5)
  else 3*Real.pi/2 + Real.arctan (2*t-7)

/-- The slope in the local first-coordinate chart of each side. -/
def squareRaySlope (t : ℝ) : ℝ :=
  if t ≤ 1 then 2*t-1 else if t ≤ 2 then 2*t-3
  else if t ≤ 3 then 2*t-5 else 2*t-7

/-- Positive scale of the actual square point relative to its unit ray. -/
def squareRayScale (t : ℝ) : ℝ := (Real.cos (Real.arctan (squareRaySlope t)))⁻¹

theorem squareRayScale_pos (t : ℝ) : 0 < squareRayScale t :=
  inv_pos.mpr (Real.cos_arctan_pos _)

private theorem arctan_neg_one : Real.arctan (-1) = -Real.pi/4 := by
  rw [Real.arctan_neg, Real.arctan_one]; ring

private theorem arctan_slope_bounds {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) :
    -Real.pi/4 ≤ Real.arctan x ∧ Real.arctan x ≤ Real.pi/4 := by
  constructor
  · simpa only [arctan_neg_one] using Real.arctan_mono hx.1
  · simpa only [Real.arctan_one] using Real.arctan_mono hx.2

private theorem arctan_slope_strict_lower {x : ℝ} (hx : -1 < x) :
    -Real.pi/4 < Real.arctan x := by
  simpa only [arctan_neg_one] using Real.arctan_strictMono hx

private theorem arctan_slope_strict_upper {x : ℝ} (hx : x < 1) :
    Real.arctan x < Real.pi/4 := by
  simpa only [Real.arctan_one] using Real.arctan_strictMono hx

theorem squareRayAngle_strictMonoOn : StrictMonoOn squareRayAngle (Set.Icc 0 4) := by
  intro a ha b hb hab
  have hm (k : ℝ) : Real.arctan (2*a-k) < Real.arctan (2*b-k) :=
    Real.arctan_strictMono (by linarith)
  unfold squareRayAngle
  split_ifs <;>
    first
    | linarith [hm 1, hm 3, hm 5, hm 7]
    | (have hu := arctan_slope_strict_upper (by linarith : 2*a-7 < 1);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-7);
       linarith [Real.pi_pos])
    | (have hu := arctan_slope_bounds (show -1 ≤ 2*a-1 ∧ 2*a-1 ≤ 1 by constructor <;> linarith [ha.1]);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-3);
       linarith [Real.pi_pos])
    | (have hu := arctan_slope_bounds (show -1 ≤ 2*a-1 ∧ 2*a-1 ≤ 1 by constructor <;> linarith [ha.1]);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-5);
       linarith [Real.pi_pos])
    | (have hu := arctan_slope_bounds (show -1 ≤ 2*a-1 ∧ 2*a-1 ≤ 1 by constructor <;> linarith [ha.1]);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-7);
       linarith [Real.pi_pos])
    | (have hu := arctan_slope_bounds (show -1 ≤ 2*a-3 ∧ 2*a-3 ≤ 1 by constructor <;> linarith);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-5);
       linarith [Real.pi_pos])
    | (have hu := arctan_slope_bounds (show -1 ≤ 2*a-3 ∧ 2*a-3 ≤ 1 by constructor <;> linarith);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-7);
       linarith [Real.pi_pos])
    | (have hu := arctan_slope_bounds (show -1 ≤ 2*a-5 ∧ 2*a-5 ≤ 1 by constructor <;> linarith);
       have hl := arctan_slope_strict_lower (by linarith : -1 < 2*b-7);
       linarith [Real.pi_pos])

@[simp] theorem squareRayAngle_zero : squareRayAngle 0 = -Real.pi/4 := by
  simp [squareRayAngle]; ring

@[simp] theorem squareRayAngle_four : squareRayAngle 4 = 7*Real.pi/4 := by
  norm_num [squareRayAngle, Real.arctan_one]; ring

theorem squareRayAngle_bounds {t : ℝ} (ht : 0 ≤ t ∧ t < 4) :
    -Real.pi/4 ≤ squareRayAngle t ∧ squareRayAngle t < 7*Real.pi/4 := by
  constructor
  · simpa using squareRayAngle_strictMonoOn.monotoneOn
      (show (0:ℝ) ∈ Set.Icc 0 4 by norm_num) ⟨ht.1, ht.2.le⟩ ht.1
  · simpa using squareRayAngle_strictMonoOn ⟨ht.1, ht.2.le⟩
      (show (4:ℝ) ∈ Set.Icc 0 4 by norm_num) ht.2

private theorem inv_cos_mul_sin_arctan (x : ℝ) :
    (Real.cos (Real.arctan x))⁻¹ * Real.sin (Real.arctan x) = x := by
  rw [Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1+x^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

/-- Equality of actual complex vectors, not just a cyclic-order certificate. -/
theorem twoCenterSquare_eq_scaled_circle (t : ℝ) :
    twoCenterSquare t = (squareRayScale t : ℂ) * circleMap 0 1 (squareRayAngle t) := by
  have hcos (x : ℝ) : (Real.cos (Real.arctan x))⁻¹ * Real.cos (Real.arctan x) = 1 :=
    inv_mul_cancel₀ (ne_of_gt (Real.cos_arctan_pos x))
  have h3 : 3*Real.pi/2 = Real.pi + Real.pi/2 := by ring
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, circleMap_zero_re, circleMap_zero_im, one_mul] <;>
    unfold twoCenterSquare squareRayScale squareRaySlope squareRayAngle <;>
    split_ifs <;> simp only [h3, Real.cos_add, Real.sin_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi,
      zero_mul, one_mul, neg_mul, mul_neg, mul_zero, zero_sub, sub_zero,
      zero_add, add_zero, neg_neg, hcos, inv_cos_mul_sin_arctan] <;> ring

/-- The real lift is continuous even across the four chart boundaries. -/
theorem squareRayAngle_continuous : Continuous squareRayAngle := by
  unfold squareRayAngle
  apply continuous_if_le continuous_id continuous_const
  · apply Continuous.continuousOn; fun_prop
  · apply Continuous.continuousOn
    apply continuous_if_le continuous_id continuous_const
    · apply Continuous.continuousOn; fun_prop
    · apply Continuous.continuousOn
      apply continuous_if_le continuous_id continuous_const
      · apply Continuous.continuousOn; fun_prop
      · apply Continuous.continuousOn; fun_prop
      · intro t ht; change t = 3 at ht; subst t
        norm_num [Real.arctan_one, Real.arctan_neg]; ring
    · intro t ht; change t = 2 at ht; subst t
      norm_num [Real.arctan_one, Real.arctan_neg]; ring
  · intro t ht; change t = 1 at ht; subst t
    norm_num [Real.arctan_one, Real.arctan_neg]; ring

/-- A genuine common local frame with actual, positively scaled endpoints.
The existing `Fin` labels are retained verbatim, including the marked first. -/
structure OrderedRayAngles {n : ℕ} (ray : Fin n → ℂ) where
  rotation : ℂ
  rotation_ne_zero : rotation ≠ 0
  angle : Fin n → ℝ
  angle_strictMono : StrictMono angle
  angle_pos : ∀ i, 0 < angle i
  angle_lt_one : ∀ i, angle i < 1
  radius : Fin n → ℝ
  radius_pos : ∀ i, 0 < radius i
  point_eq : ∀ i, ray i = rotation * ((radius i : ℝ) : ℂ) * boundaryPoint (angle i)

/-- Convert any finite strictly ordered lift of width below one turn into
open unit-turn coordinates, without cyclically shifting any port. -/
theorem orderedRayAngles_of_lift {n : ℕ} (ray : Fin n → ℂ)
    (rotation : ℂ) (hrot : rotation ≠ 0) (theta radius : Fin n → ℝ)
    (hmono : StrictMono theta) (hradius : ∀ i, 0 < radius i)
    (hpoint : ∀ i, ray i = rotation * (radius i : ℂ) * circleMap 0 1 (theta i))
    (L U : ℝ) (hLU : U-L < 2*Real.pi)
    (hL : ∀ i, L ≤ theta i) (hU : ∀ i, theta i ≤ U) :
    Nonempty (OrderedRayAngles ray) := by
  let cut := (L + U - 2*Real.pi)/2
  have hcut : cut < L := by dsimp [cut]; linarith
  have hcutU : U < cut + 2*Real.pi := by dsimp [cut]; linarith
  refine ⟨{
    rotation := rotation * circleMap 0 1 cut
    rotation_ne_zero := mul_ne_zero hrot ?_
    angle := fun i => (theta i-cut)/(2*Real.pi)
    angle_strictMono := ?_
    angle_pos := ?_
    angle_lt_one := ?_
    radius := radius
    radius_pos := hradius
    point_eq := ?_ }⟩
  · exact circleMap_ne_center (by norm_num)
  · intro i j hij
    exact (div_lt_div_iff_of_pos_right (by positivity : 0 < 2*Real.pi)).mpr
      (sub_lt_sub_right (hmono hij) cut)
  · intro i
    exact div_pos (sub_pos.mpr (hcut.trans_le (hL i))) (by positivity)
  · intro i
    apply (div_lt_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [hU i]
  · intro i
    rw [hpoint i]
    have ha : 2*Real.pi*((theta i-cut)/(2*Real.pi)) = theta i-cut := by
      field_simp
    simp only [boundaryPoint, ha]
    calc
      _ = rotation * (radius i : ℂ) *
          (circleMap 0 1 cut * circleMap 0 1 (theta i-cut)) := by
        rw [circleMap_zero_mul]; simp
      _ = _ := by ring

/-- Every source-model positive port order has actual open-turn angular
coordinates in one common orientation-preserving local frame. -/
theorem positivePortOrder_orderedRayAngles {n : ℕ} {vertex : ℂ}
    {arc : Fin n → unitInterval → ℂ}
    (P : LabelledInstance.PositivePortOrder vertex arc) :
    Nonempty (OrderedRayAngles
      (fun i => P.speed i • (P.rotation * twoCenterSquare (P.time i)))) := by
  cases n with
  | zero =>
    exact ⟨{
      rotation := 1
      rotation_ne_zero := one_ne_zero
      angle := Fin.elim0
      angle_strictMono := by intro i; exact Fin.elim0 i
      angle_pos := by intro i; exact Fin.elim0 i
      angle_lt_one := by intro i; exact Fin.elim0 i
      radius := Fin.elim0
      radius_pos := by intro i; exact Fin.elim0 i
      point_eq := by intro i; exact Fin.elim0 i }⟩
  | succ n =>
    apply orderedRayAngles_of_lift _ P.rotation P.rotation_ne_zero
      (fun i => squareRayAngle (P.time i))
      (fun i => P.speed i * squareRayScale (P.time i))
      (L := -Real.pi/4) (U := squareRayAngle (P.time (Fin.last n)))
    · intro i j hij
      exact squareRayAngle_strictMonoOn
        ⟨(P.time_range i).1, (P.time_range i).2.le⟩
        ⟨(P.time_range j).1, (P.time_range j).2.le⟩ (P.time_strictMono hij)
    · intro i; exact mul_pos (P.speed_pos i) (squareRayScale_pos _)
    · intro i
      rw [twoCenterSquare_eq_scaled_circle, Complex.real_smul, Complex.ofReal_mul]
      ring
    · linarith [(squareRayAngle_bounds (P.time_range (Fin.last n))).2]
    · intro i; exact (squareRayAngle_bounds (P.time_range i)).1
    · intro i
      exact squareRayAngle_strictMonoOn.monotoneOn
        ⟨(P.time_range i).1, (P.time_range i).2.le⟩
        ⟨(P.time_range (Fin.last n)).1, (P.time_range (Fin.last n)).2.le⟩
        (P.time_strictMono.monotone (Fin.le_last i))

/-- Positive rescaling changes only radii, never angles, labels, or the cut. -/
def OrderedRayAngles.positiveScale {n : ℕ} {ray : Fin n → ℂ}
    (A : OrderedRayAngles ray) (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) :
    OrderedRayAngles (fun i => s i • ray i) where
  rotation := A.rotation
  rotation_ne_zero := A.rotation_ne_zero
  angle := A.angle
  angle_strictMono := A.angle_strictMono
  angle_pos := A.angle_pos
  angle_lt_one := A.angle_lt_one
  radius := fun i => s i * A.radius i
  radius_pos i := mul_pos (hs i) (A.radius_pos i)
  point_eq i := by rw [Complex.real_smul, A.point_eq i, Complex.ofReal_mul]; ring

/-- Actual cut points on the prescribed radial germs inherit the proved order,
including unequal distances from the vertex. -/
theorem positivePortOrder_germ_orderedRayAngles {n : ℕ} {vertex : ℂ}
    {arc : Fin n → unitInterval → ℂ}
    (P : LabelledInstance.PositivePortOrder vertex arc)
    (t : Fin n → unitInterval) (ht : ∀ i, 0 < t i) (htP : ∀ i, t i ≤ P.radius) :
    Nonempty (OrderedRayAngles (fun i => arc i (t i) - vertex)) := by
  obtain ⟨A⟩ := positivePortOrder_orderedRayAngles P
  have he : (fun i => arc i (t i) - vertex) =
      (fun i => (t i : ℝ) • (P.speed i • (P.rotation * twoCenterSquare (P.time i)))) := by
    funext i
    rw [P.germ i (t i) (htP i), add_sub_cancel_left]
  rw [he]
  exact ⟨A.positiveScale (fun i => (t i : ℝ)) (fun i => ht i)⟩

end
end MatchgateWidth
