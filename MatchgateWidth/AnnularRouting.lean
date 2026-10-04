import MatchgateWidth.PlanarDrawing

/-! # Disjoint ordered annular connectors
Angular interpolation aligns any two strictly ordered boundary-port lists.
The radius is strictly increasing, so no output nonintersection is assumed.
-/
namespace MatchgateWidth
noncomputable section

def affineBlend (a b : ℝ) (t : unitInterval) : ℝ := (1-(t:ℝ))*a+(t:ℝ)*b

theorem affineBlend_pos {a b : ℝ} (ha : 0<a) (hb : 0<b) (t : unitInterval) :
    0 < affineBlend a b t := by
  by_cases ht : (t:ℝ)=1
  · simp [affineBlend, ht, hb]
  · have ht' : 0 < 1-(t:ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 ht)
    have hp := mul_pos ht' ha
    have hq := mul_nonneg t.property.1 hb.le
    dsimp [affineBlend]
    linarith

theorem affineBlend_lt_one {a b : ℝ} (ha : a<1) (hb : b<1) (t : unitInterval) :
    affineBlend a b t < 1 := by
  have h := affineBlend_pos (sub_pos.mpr ha) (sub_pos.mpr hb) t
  dsimp [affineBlend] at *
  nlinarith

theorem affineBlend_strictMono {ι : Type*} [Preorder ι] (a b : ι → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) (t : unitInterval) :
    StrictMono (fun i => affineBlend (a i) (b i) t) := by
  intro i j hij
  have h := affineBlend_pos (sub_pos.mpr (ha hij)) (sub_pos.mpr (hb hij)) t
  dsimp [affineBlend] at *
  nlinarith

theorem boundaryPoint_inj_on_turn {a b : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (hb0 : 0<b) (hb1 : b<1) (h : boundaryPoint a = boundaryPoint b) : a=b := by
  have hp : 0 < 2*Real.pi := by positivity
  have he := injOn_circleMap_of_abs_sub_le' (c := (0:ℂ)) (R := 1)
    (a := 0) (b := 2*Real.pi) (by norm_num) (by simp)
    (show 2*Real.pi*a ∈ Set.Ico 0 (2*Real.pi) by constructor <;> nlinarith)
    (show 2*Real.pi*b ∈ Set.Ico 0 (2*Real.pi) by constructor <;> nlinarith) h
  nlinarith

def annularConnector (c : ℂ) (R S a b : ℝ) :
    Path (c+(R:ℂ)*boundaryPoint a) (c+(S:ℂ)*boundaryPoint b) where
  toFun t := c+((affineBlend R S t : ℝ):ℂ)*boundaryPoint (affineBlend a b t)
  continuous_toFun := by
    unfold affineBlend boundaryPoint circleMap
    fun_prop
  source' := by simp [affineBlend]
  target' := by simp [affineBlend]

theorem annularConnector_norm (c : ℂ) {R S : ℝ} (hR : 0<R) (hS : 0<S)
    (a b : ℝ) (t : unitInterval) :
    ‖annularConnector c R S a b t-c‖ = affineBlend R S t := by
  change ‖c+((affineBlend R S t : ℝ):ℂ)*boundaryPoint (affineBlend a b t)-c‖ = _
  rw [add_sub_cancel_left, norm_mul, norm_boundaryPoint, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (affineBlend_pos hR hS t)]

theorem annularConnector_parameter_eq (c : ℂ) {R S : ℝ} (hR : 0<R) (hRS : R<S)
    {a b a' b' : ℝ} {t u : unitInterval}
    (h : annularConnector c R S a b t = annularConnector c R S a' b' u) : t=u := by
  have he := congrArg (fun z => ‖z-c‖) h
  rw [annularConnector_norm c hR (hR.trans hRS),
    annularConnector_norm c hR (hR.trans hRS)] at he
  apply Subtype.ext
  dsimp [affineBlend] at he
  nlinarith

theorem annularConnector_injective (c : ℂ) {R S : ℝ} (hR : 0<R) (hRS : R<S)
    (a b : ℝ) : Function.Injective (annularConnector c R S a b) :=
  fun _ _ h => annularConnector_parameter_eq c hR hRS h

/-- Every pair of distinct ordered port connectors is genuinely disjoint,
including their endpoints. -/
theorem annularConnectors_disjoint {n : ℕ} (c : ℂ) {R S : ℝ}
    (hR : 0<R) (hRS : R<S) (a b : Fin n → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : ∀ i, 0<a i) (ha1 : ∀ i, a i<1)
    (hb0 : ∀ i, 0<b i) (hb1 : ∀ i, b i<1) :
    Pairwise (fun i j => Disjoint (Set.range (annularConnector c R S (a i) (b i)))
      (Set.range (annularConnector c R S (a j) (b j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨t,rfl⟩ ⟨u,hu⟩
  have htu := annularConnector_parameter_eq c hR hRS hu
  subst u
  have hr : ((affineBlend R S t : ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (affineBlend_pos hR (hR.trans hRS) t))
  have he : boundaryPoint (affineBlend (a j) (b j) t) =
      boundaryPoint (affineBlend (a i) (b i) t) := by
    apply mul_left_cancel₀ hr
    exact add_left_cancel hu
  have hab := boundaryPoint_inj_on_turn
    (affineBlend_pos (ha0 j) (hb0 j) t) (affineBlend_lt_one (ha1 j) (hb1 j) t)
    (affineBlend_pos (ha0 i) (hb0 i) t) (affineBlend_lt_one (ha1 i) (hb1 i) t) he
  exact hij ((affineBlend_strictMono a b ha hb t).injective hab).symm

/-- Interior connector points lie strictly between the two carrier circles. -/
theorem annularConnector_in_open_annulus (c : ℂ) {R S : ℝ}
    (hR : 0<R) (hRS : R<S) (a b : ℝ) (t : unitInterval)
    (ht0 : 0<t) (ht1 : t<1) :
    R < ‖annularConnector c R S a b t-c‖ ∧
      ‖annularConnector c R S a b t-c‖ < S := by
  rw [annularConnector_norm c hR (hR.trans hRS)]
  have hp := mul_pos (show 0<(t:ℝ) from ht0) (sub_pos.mpr hRS)
  have hq := mul_pos (show 0<1-(t:ℝ) from sub_pos.mpr ht1) (sub_pos.mpr hRS)
  dsimp [affineBlend]
  constructor <;> nlinarith

/-- Closed endpoint-inclusive bounds permit insertion into a prescribed local disk. -/
theorem annularConnector_in_closed_annulus (c : ℂ) {R S : ℝ}
    (hR : 0<R) (hRS : R<S) (a b : ℝ) (t : unitInterval) :
    R ≤ ‖annularConnector c R S a b t-c‖ ∧
      ‖annularConnector c R S a b t-c‖ ≤ S := by
  rw [annularConnector_norm c hR (hR.trans hRS)]
  have hp := mul_nonneg t.property.1 (sub_nonneg.mpr hRS.le)
  have hq := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hRS.le)
  dsimp [affineBlend]
  constructor <;> nlinarith

end
end MatchgateWidth
