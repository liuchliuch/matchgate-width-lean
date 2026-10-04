import MatchgateWidth.LocalConnectorBank
import MatchgateWidth.AllLeftCutAngles

/-! # Fixed-size connector banks in the derived round source collars

The local frame may have arbitrary nonzero norm. The physical inserted graph
radius is r/4, the angular interpolation finishes by r/2, and the whole bank
stays in radius 3r. Parameters are calculated in the actual local frame.
-/
namespace MatchgateWidth
noncomputable section
namespace OrderedRayAngles
variable {n : ℕ} {p : Fin n → ℂ} (A : OrderedRayAngles p)

theorem norm_point (i : Fin n) : ‖p i‖ = ‖A.rotation‖ * A.radius i := by
  rw [A.point_eq,norm_mul,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (A.radius_pos i)]

/-- The inserted local drawing is scaled in exactly the connector's frame. -/
def collarFactor (r : ℝ) : ℂ := A.rotation * ((r/(4*‖A.rotation‖):ℝ):ℂ)

theorem collarFactor_ne_zero {r : ℝ} (hr : 0 < r) : A.collarFactor r ≠ 0 := by
  apply mul_ne_zero A.rotation_ne_zero
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr A.rotation_ne_zero)))

theorem norm_collarFactor {r : ℝ} (hr : 0 < r) : ‖A.collarFactor r‖ = r/4 := by
  have hn : 0 < ‖A.rotation‖ := norm_pos_iff.mpr A.rotation_ne_zero
  rw [collarFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (div_pos hr (mul_pos (by norm_num) hn))]
  field_simp

/-- Physical radii are uniform even when the local ordered frame is nonunit. -/
theorem radius_eq_of_round_cut {r : ℝ} (hround : ∀ i, ‖p i‖ = 2*r) (i : Fin n) :
    A.radius i = 2*r/‖A.rotation‖ := by
  apply (eq_div_iff (norm_ne_zero_iff.mpr A.rotation_ne_zero)).mpr
  rw [mul_comm,← A.norm_point]
  exact hround i

/-- Actual connector-bank existence at canonical physical source-collar sizes.
Every path is the explicit jointly-continuous formula used for stage separation. -/
theorem exists_roundCollarBank {k : ℕ} (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hround : ∀ i, ‖p i‖ = 2*r) (w : Fin n → ℂ) (d : Fin n → Fin k → ℝ)
    (horder : ∀ i j l, j < l → 0 < (d i l-d i j)*orientedArea (p i) (w i))
    (α : Fin (n*k) → ℝ) (hα : StrictMono α)
    (hα0 : ∀ q, 0 < α q) (hα1 : ∀ q, α q < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : LocalConnectorBank c A.rotation (r/(4*‖A.rotation‖)) (3*r/‖A.rotation‖)
        α (A.blockEndpoint w d ε),
        (∀ q u, B.path q u = A.localBlockConnector c w d α
          (r/(4*‖A.rotation‖)) (r/(2*‖A.rotation‖)) ε q u) := by
  have hn : 0 < ‖A.rotation‖ := norm_pos_iff.mpr A.rotation_ne_zero
  have hR : 0 < r/(4*‖A.rotation‖) := div_pos hr (mul_pos (by norm_num) hn)
  have hRS : r/(4*‖A.rotation‖) < r/(2*‖A.rotation‖) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  apply A.exists_localConnectorBank c w d horder α hα hα0 hα1 _ _ _ hR hRS
  · intro i
    rw [A.radius_eq_of_round_cut hround i]
    apply (div_lt_div_iff₀ (by positivity) hn).mpr
    nlinarith
  · intro i
    rw [A.radius_eq_of_round_cut hround i]
    exact (div_lt_div_iff_of_pos_right hn).mpr (by linarith)

/-- The canonical bank's actual support stays in physical radius 3r. -/
theorem roundCollarBank_bound {k : ℕ} (c : ℂ) (r : ℝ) (α : Fin k → ℝ)
    (endpoint : Fin k → ℂ)
    (B : LocalConnectorBank c A.rotation (r/(4*‖A.rotation‖)) (3*r/‖A.rotation‖) α endpoint)
    (q : Fin k) (u : unitInterval) : dist (B.path q u) c ≤ 3*r := by
  have hn : ‖A.rotation‖ ≠ 0 := norm_ne_zero_iff.mpr A.rotation_ne_zero
  have he : ‖A.rotation‖*(3*r/‖A.rotation‖) = 3*r := by field_simp
  simpa only [he] using B.bound q u

/-- The canonical bank meets the actual inserted disk only at its start. -/
theorem roundCollarBank_inner_only_start {k : ℕ} (c : ℂ) (r : ℝ)
    (α : Fin k → ℝ) (endpoint : Fin k → ℂ)
    (B : LocalConnectorBank c A.rotation (r/(4*‖A.rotation‖)) (3*r/‖A.rotation‖) α endpoint)
    (q : Fin k) (u : unitInterval) (hu : dist (B.path q u) c ≤ r/4) : u = 0 := by
  have hn : ‖A.rotation‖ ≠ 0 := norm_ne_zero_iff.mpr A.rotation_ne_zero
  have he : ‖A.rotation‖*(r/(4*‖A.rotation‖)) = r/4 := by field_simp
  exact B.inner_only_start q u (by simpa only [he] using hu)

end OrderedRayAngles
end
end MatchgateWidth
