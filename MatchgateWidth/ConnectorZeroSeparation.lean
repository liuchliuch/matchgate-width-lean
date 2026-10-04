import MatchgateWidth.LocalConnectorBank
import MatchgateWidth.CompactCurvePerturbation

/-! # Source-radius separation of local connector reference traces

The zero-width local connector reaches its cut circle only at its own terminal
cutpoint. Therefore it misses every original corridor piece outside that circle
which does not contain that cutpoint. Compact perturbation turns these derived
reference separations into uniform separation of the actual nonzero-width
connector and wire stages.
-/
namespace MatchgateWidth
noncomputable section
namespace OrderedRayAngles
variable {n r : ℕ} {p : Fin n → ℂ} (A : OrderedRayAngles p)

private theorem norm_ray_point (i : Fin n) : ‖p i‖ = ‖A.rotation‖ * A.radius i := by
  rw [A.point_eq]
  simp [Complex.norm_real,abs_of_pos (A.radius_pos i)]

/-- At zero width a connector hits its original cut circle only at the end,
regardless of how far around the inner annulus its native port began. -/
theorem localBlockConnector_zero_at_cut (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S : ℝ)
    (hR : 0 < R) (hRS : R < S) (hS : ∀ i, S ≤ A.radius i)
    (q : Fin (n*r)) (t : unitInterval)
    (hcut : ‖p (finProdFinEquiv.symm q).1‖ ≤
      dist (A.localBlockConnector c w d α R S 0 q t) c) : t = 1 := by
  have hρ : ∀ q, S ≤ A.blockRadius w d 0 q := by intro q; simpa using hS (finProdFinEquiv.symm q).1
  rw [A.localBlockConnector_norm c w d α R S 0 hR hRS hρ,
    A.blockRadius_zero,A.norm_ray_point] at hcut
  have hn : 0 < ‖A.rotation‖ := norm_pos_iff.mpr A.rotation_ne_zero
  have hh := (mul_le_mul_iff_right₀ hn).mp hcut
  have hri : R < A.radius (finProdFinEquiv.symm q).1 := hRS.trans_le (hS _)
  apply Subtype.ext
  change (t : ℝ) = 1
  dsimp [affineBlend] at hh
  nlinarith [t.property.2]

theorem localBlockConnector_zero_target (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S : ℝ)
    (hRS : R < S) (hS : ∀ i, S ≤ A.radius i) (q : Fin (n*r)) :
    A.localBlockConnector c w d α R S 0 q 1 = c + p (finProdFinEquiv.symm q).1 := by
  have hρ : ∀ q, S ≤ A.blockRadius w d 0 q := by intro q; simpa using hS (finProdFinEquiv.symm q).1
  have hden : ∀ i k, 0 < 1+((0:ℝ)*d i k)*(w i/p i).re := by intro i k; norm_num
  calc
    _ = c + A.blockEndpoint w d 0 q := (A.localBlockConnectorPath c w d α R S 0 hRS hρ hden q).target
    _ = _ := by simp [blockEndpoint]

/-- Source cut-radius inequalities and exclusion of the original cutpoint
prove actual zero-width connector/corridor disjointness. No connector-stage
nonintersection assumption is present. -/
theorem localBlockConnector_zero_disjoint_of_outside (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S : ℝ)
    (hR : 0 < R) (hRS : R < S) (hS : ∀ i, S ≤ A.radius i)
    (q : Fin (n*r)) (F : Set ℂ)
    (hF : ∀ z ∈ F, ‖p (finProdFinEquiv.symm q).1‖ ≤ dist z c)
    (hpoint : c + p (finProdFinEquiv.symm q).1 ∉ F) :
    Disjoint (Set.range (A.localBlockConnector c w d α R S 0 q)) F := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,rfl⟩ hz
  have ht := A.localBlockConnector_zero_at_cut c w d α R S hR hRS hS q t (hF _ hz)
  apply hpoint
  simpa only [ht,A.localBlockConnector_zero_target c w d α R S hRS hS q] using hz

/-- A genuine nonincident source corridor piece stays disjoint from the
actual local annular connector for all sufficiently small independent widths.
The original cutpoint exclusion is supplied by source incidence/simplicity. -/
theorem exists_connector_piece_separation (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S : ℝ)
    (hR : 0 < R) (hRS : R < S) (hS : ∀ i, S ≤ A.radius i)
    (q : Fin (n*r)) (f : ℝ → unitInterval → ℂ)
    (hf0 : Continuous (f 0))
    (hf : ∀ t, ContinuousAt (fun z : ℝ × unitInterval => f z.1 z.2) (0,t))
    (hout : ∀ t, ‖p (finProdFinEquiv.symm q).1‖ ≤ dist (f 0 t) c)
    (hpoint : c + p (finProdFinEquiv.symm q).1 ∉ Set.range (f 0)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε η : ℝ, |ε| < ε₀ → |η| < ε₀ →
      Disjoint (Set.range (A.localBlockConnector c w d α R S ε q)) (Set.range (f η)) := by
  have hρ : ∀ q, S ≤ A.blockRadius w d 0 q := by intro q; simpa using hS (finProdFinEquiv.symm q).1
  have hden : ∀ i k, 0 < 1+((0:ℝ)*d i k)*(w i/p i).re := by intro i k; norm_num
  have hc0 : Continuous (A.localBlockConnector c w d α R S 0 q) :=
    (A.localBlockConnectorPath c w d α R S 0 hRS hρ hden q).continuous
  have hdis := A.localBlockConnector_zero_disjoint_of_outside c w d α R S hR hRS hS q
    (Set.range (f 0)) (by rintro z ⟨t,rfl⟩; exact hout t) hpoint
  obtain ⟨ρ,hρpos,hsep⟩ := hdis.exists_thickenings (isCompact_range hc0) (isCompact_range hf0).isClosed
  obtain ⟨ε,hε,hεspec⟩ := compact_curve_perturbation_radius
    (fun ε t => A.localBlockConnector c w d α R S ε q t)
    (A.localBlockConnector_continuousAt_zero c w d α R S q)
    Metric.isOpen_thickening (Metric.self_subset_thickening hρpos _)
  obtain ⟨η,hη,hηspec⟩ := compact_curve_perturbation_radius f hf
    Metric.isOpen_thickening (Metric.self_subset_thickening hρpos _)
  exact ⟨min ε η,lt_min hε hη,fun ε' η' he' hη' => hsep.mono
    (hεspec ε' (he'.trans_le (min_le_left _ _)))
    (hηspec η' (hη'.trans_le (min_le_right _ _)))⟩

end OrderedRayAngles
end
end MatchgateWidth
