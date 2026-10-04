import MatchgateWidth.PrimitiveAllLeftGadget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Arbitrary-arity ordered radial primitive drawings

Every port is drawn from the origin to a distinct first-quadrant circle point.
The slope, arctangent boundary angle, square parameter, and positive radial
speed are all explicit. Thus no embedding-normalization or order-existence
hypothesis is needed even for arbitrary primitive arity.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget

/-- Increasing positive slopes strictly below one. -/
def primitiveRaySlope {n : ℕ} (i : Fin n) : ℝ := (i.val + 1) / (n + 1)

theorem primitiveRaySlope_bounds {n : ℕ} (i : Fin n) :
    0 < primitiveRaySlope i ∧ primitiveRaySlope i < 1 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  constructor
  · unfold primitiveRaySlope; positivity
  · exact (div_lt_one hn).mpr (by linarith)

theorem primitiveRaySlope_strictMono {n : ℕ} :
    StrictMono (primitiveRaySlope (n := n)) := by
  intro i j hij
  have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
  exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < n + 1)).mpr (by linarith)

/-- The angle is in turns, exactly as required by the ordered disk model. -/
def primitiveRayAngle {n : ℕ} (i : Fin n) : ℝ :=
  Real.arctan (primitiveRaySlope i) / (2 * Real.pi)

theorem primitiveRayAngle_phase {n : ℕ} (i : Fin n) :
    2 * Real.pi * primitiveRayAngle i = Real.arctan (primitiveRaySlope i) := by
  unfold primitiveRayAngle
  exact mul_div_cancel₀ _ (by positivity)

theorem primitiveRayAngle_pos {n : ℕ} (i : Fin n) : 0 < primitiveRayAngle i :=
  div_pos (Real.arctan_pos.mpr (primitiveRaySlope_bounds i).1) (by positivity)

theorem primitiveRayAngle_lt_one {n : ℕ} (i : Fin n) : primitiveRayAngle i < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
  linarith [Real.arctan_lt_pi_div_two (primitiveRaySlope i), Real.pi_pos]

theorem primitiveRayAngle_strictMono {n : ℕ} :
    StrictMono (primitiveRayAngle (n := n)) := by
  intro i j hij
  exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    (Real.arctan_strictMono (primitiveRaySlope_strictMono hij))

/-- The actual circle endpoints, with no quotient or unchosen phase. -/
def primitiveRayPoint {n : ℕ} (i : Fin n) : ℂ := boundaryPoint (primitiveRayAngle i)

theorem primitiveRayPoint_injective {n : ℕ} :
    Function.Injective (primitiveRayPoint (n := n)) := by
  intro i j h
  have him := congrArg Complex.im h
  simp only [primitiveRayPoint, boundaryPoint_im, primitiveRayAngle_phase] at him
  exact (Real.sin_arctan_strictMono.comp primitiveRaySlope_strictMono).injective him

/-- The first side of the positively traversed square parametrization. -/
def primitiveRayTime {n : ℕ} (i : Fin n) : ℝ := (1 + primitiveRaySlope i) / 2

theorem primitiveRayTime_strictMono {n : ℕ} :
    StrictMono (primitiveRayTime (n := n)) := by
  intro i j hij
  dsimp [primitiveRayTime]
  linarith [primitiveRaySlope_strictMono hij]

theorem primitiveRayTime_range {n : ℕ} (i : Fin n) :
    0 ≤ primitiveRayTime i ∧ primitiveRayTime i < 4 := by
  dsimp [primitiveRayTime]
  constructor <;> linarith [(primitiveRaySlope_bounds i).1, (primitiveRaySlope_bounds i).2]

theorem primitiveRayPoint_eq_square {n : ℕ} (i : Fin n) :
    primitiveRayPoint i = Real.cos (Real.arctan (primitiveRaySlope i)) •
      twoCenterSquare (primitiveRayTime i) := by
  have ht : primitiveRayTime i ≤ 1 := by
    dsimp [primitiveRayTime]
    linarith [(primitiveRaySlope_bounds i).2]
  rw [twoCenterSquare, ite_eq_left ht]
  rw [Complex.real_smul]
  apply Complex.ext
  · simp only [primitiveRayPoint, boundaryPoint_re, primitiveRayAngle_phase,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, 
      zero_mul, sub_zero, mul_one]
  · simp only [primitiveRayPoint, boundaryPoint_im, primitiveRayAngle_phase,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Real.sin_arctan, Real.cos_arctan]
    dsimp [primitiveRayTime]
    ring

/-- An explicit positive ordered radial configuration for every finite arity. -/
def radialPortConfiguration (n : ℕ) : RadialPortConfiguration n where
  point := primitiveRayPoint
  norm_point i := norm_boundaryPoint _
  point_injective := primitiveRayPoint_injective
  angle := primitiveRayAngle
  angle_pos := primitiveRayAngle_pos
  angle_lt_one := primitiveRayAngle_lt_one
  angle_strictMono := primitiveRayAngle_strictMono
  point_eq_boundary _ := rfl
  time := primitiveRayTime
  time_strictMono := primitiveRayTime_strictMono
  time_range := primitiveRayTime_range
  speed i := Real.cos (Real.arctan (primitiveRaySlope i))
  speed_pos i := Real.cos_arctan_pos _
  point_eq_square := primitiveRayPoint_eq_square

/-- Every original primitive occurs as an actual connected ordered disk gadget
with precisely its original boundary order and tensor, at arbitrary arity. -/
theorem primitive_orderedPlanar {S : LabelledShape} (l : S.LeftLabel) :
    Nonempty (primitive l).OrderedPlanar :=
  ⟨primitiveOrderedPlanar l (radialPortConfiguration _)⟩

end AllLeftGadget
end
end MatchgateWidth
