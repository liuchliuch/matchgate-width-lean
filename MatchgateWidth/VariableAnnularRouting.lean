import MatchgateWidth.AnnularRouting
import Mathlib.Topology.Order.ProjIcc

/-! # Ordered annular connectors to unequal endpoint radii
All angle interpolation is completed at one common intermediate radius.
Thereafter each connector follows its own radial ray, so unequal endpoint
radii do not compromise disjointness.
-/
namespace MatchgateWidth
noncomputable section

def annularLevel (R S r : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((r-R)/(S-R))

theorem annularLevel_start (R S : ℝ) : annularLevel R S R = 0 := by
  simp [annularLevel]

theorem annularLevel_end {R S r : ℝ} (hRS : R<S) (hSr : S≤r) : annularLevel R S r = 1 := by
  apply projIcc_eq_one.mpr
  exact (le_div_iff₀ (sub_pos.mpr hRS)).mpr (by linarith)

def variableAnnularConnector (c : ℂ) (R S ρ a b : ℝ)
    (hRS : R<S) (hSρ : S≤ρ) :
    Path (c+(R:ℂ)*boundaryPoint a) (c+(ρ:ℂ)*boundaryPoint b) where
  toFun t := c+((affineBlend R ρ t : ℝ):ℂ)*boundaryPoint
    (affineBlend a b (annularLevel R S (affineBlend R ρ t)))
  continuous_toFun := by
    have hlevel : Continuous (annularLevel R S) := by
      unfold annularLevel
      exact continuous_projIcc.comp (by fun_prop)
    unfold affineBlend boundaryPoint circleMap
    fun_prop
  source' := by simp [affineBlend, annularLevel_start]
  target' := by simp [affineBlend, annularLevel_end hRS hSρ]

theorem variableAnnularConnector_norm (c : ℂ) {R S ρ : ℝ} (hR : 0<R)
    (hRS : R<S) (hSρ : S≤ρ) (a b : ℝ) (t : unitInterval) :
    ‖variableAnnularConnector c R S ρ a b hRS hSρ t-c‖ = affineBlend R ρ t := by
  change ‖c+((affineBlend R ρ t : ℝ):ℂ)*boundaryPoint _-c‖ = _
  rw [add_sub_cancel_left, norm_mul, norm_boundaryPoint, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (affineBlend_pos hR ((hR.trans hRS).trans_le hSρ) t)]

theorem variableAnnularConnector_injective (c : ℂ) {R S ρ : ℝ} (hR : 0<R)
    (hRS : R<S) (hSρ : S≤ρ) (a b : ℝ) :
    Function.Injective (variableAnnularConnector c R S ρ a b hRS hSρ) := by
  intro t u he
  have h := congrArg (fun z => ‖z-c‖) he
  rw [variableAnnularConnector_norm c hR,variableAnnularConnector_norm c hR] at h
  apply Subtype.ext
  have hr : R<ρ := hRS.trans_le hSρ
  dsimp [affineBlend] at h
  nlinarith

/-- Arbitrary endpoint radii beyond the common interpolation circle preserve
all pairwise port-order disjointness. -/
theorem variableAnnularConnectors_disjoint {n : ℕ} (c : ℂ) {R S : ℝ}
    (hR : 0<R) (hRS : R<S) (ρ a b : Fin n → ℝ) (hρ : ∀ i, S≤ρ i)
    (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : ∀ i, 0<a i) (ha1 : ∀ i, a i<1)
    (hb0 : ∀ i, 0<b i) (hb1 : ∀ i, b i<1) :
    Pairwise (fun i j => Disjoint
      (Set.range (variableAnnularConnector c R S (ρ i) (a i) (b i) hRS (hρ i)))
      (Set.range (variableAnnularConnector c R S (ρ j) (a j) (b j) hRS (hρ j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨t,rfl⟩ ⟨u,hu⟩
  have hr := congrArg (fun z => ‖z-c‖) hu
  rw [variableAnnularConnector_norm c hR,variableAnnularConnector_norm c hR] at hr
  have hz : ((affineBlend R (ρ i) t : ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (affineBlend_pos hR ((hR.trans hRS).trans_le (hρ i)) t))
  have he : boundaryPoint (affineBlend (a j) (b j)
      (annularLevel R S (affineBlend R (ρ i) t))) =
      boundaryPoint (affineBlend (a i) (b i)
      (annularLevel R S (affineBlend R (ρ i) t))) := by
    change c+((affineBlend R (ρ j) u : ℝ):ℂ)*boundaryPoint _ =
      c+((affineBlend R (ρ i) t : ℝ):ℂ)*boundaryPoint _ at hu
    rw [hr] at hu
    exact mul_left_cancel₀ hz (add_left_cancel hu)
  have he' := boundaryPoint_inj_on_turn
    (affineBlend_pos (ha0 j) (hb0 j) _) (affineBlend_lt_one (ha1 j) (hb1 j) _)
    (affineBlend_pos (ha0 i) (hb0 i) _) (affineBlend_lt_one (ha1 i) (hb1 i) _) he
  exact hij ((affineBlend_strictMono a b ha hb _).injective he').symm

/-- Beyond the common interpolation radius, the connector follows the exact
terminal ray. This is useful for joining a circle to a tangent cross-section. -/
theorem variableAnnularConnector_radial_tail (c : ℂ) {R S ρ : ℝ}
    (hRS : R<S) (hSρ : S≤ρ) (a b : ℝ) (t : unitInterval)
    (ht : S ≤ affineBlend R ρ t) :
    variableAnnularConnector c R S ρ a b hRS hSρ t =
      c+((affineBlend R ρ t : ℝ):ℂ)*boundaryPoint b := by
  change c+((affineBlend R ρ t : ℝ):ℂ)*boundaryPoint _ = _
  rw [annularLevel_end hRS ht]
  simp [affineBlend]

theorem variableAnnularConnector_bounds (c : ℂ) {R S ρ : ℝ} (hR : 0<R)
    (hRS : R<S) (hSρ : S≤ρ) (a b : ℝ) (t : unitInterval) :
    R ≤ ‖variableAnnularConnector c R S ρ a b hRS hSρ t-c‖ ∧
      ‖variableAnnularConnector c R S ρ a b hRS hSρ t-c‖ ≤ ρ := by
  rw [variableAnnularConnector_norm c hR]
  have hr : R<ρ := hRS.trans_le hSρ
  have hp := mul_nonneg t.property.1 (sub_nonneg.mpr hr.le)
  have hq := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hr.le)
  dsimp [affineBlend]
  constructor <;> nlinarith

end
end MatchgateWidth
