import MatchgateWidth.TransversePortAngles
import MatchgateWidth.AnnularRouting

/-! # Actual radial outer access in the original global angular frame

Outer boundary lanes use the original marked angle list and frame one. Their
terminal accesses extend the actual shifted cap endpoints radially to one
surrounding circle. Neither a cyclic relabelling nor a local-frame rotation is
introduced at the external boundary.
-/
namespace MatchgateWidth
noncomputable section
open Filter Topology
namespace OrderedRayAngles
variable {n : ℕ} {p : Fin n → ℂ} (A : OrderedRayAngles p)

theorem norm_point_of_rotation_one (hrot : A.rotation = 1) (i : Fin n) :
    ‖p i‖ = A.radius i := by
  rw [A.point_eq,hrot,one_mul,norm_mul,norm_boundaryPoint,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (A.radius_pos i)]

/-- A radial access from an actual endpoint to a common surrounding circle. -/
def outerPath (hrot : A.rotation = 1) (R : ℝ) (i : Fin n) :
    Path (p i) ((R:ℂ)*boundaryPoint (A.angle i)) :=
  (annularConnector 0 (A.radius i) R (A.angle i) (A.angle i)).cast
    (by rw [A.point_eq,hrot,one_mul,zero_add]) (by simp)

@[simp] theorem outerPath_apply (hrot : A.rotation = 1) (R : ℝ) (i : Fin n)
    (t : unitInterval) :
    A.outerPath hrot R i t = ((affineBlend (A.radius i) R t : ℝ):ℂ)*boundaryPoint (A.angle i) := by
  change 0+((affineBlend (A.radius i) R t : ℝ):ℂ)*
    boundaryPoint (affineBlend (A.angle i) (A.angle i) t) = _
  have he : affineBlend (A.angle i) (A.angle i) t = A.angle i := by unfold affineBlend; ring
  rw [zero_add,he]

theorem outerPath_norm (hrot : A.rotation = 1) {R : ℝ} (hR : 0 < R)
    (i : Fin n) (t : unitInterval) :
    ‖A.outerPath hrot R i t‖ = affineBlend (A.radius i) R t := by
  rw [A.outerPath_apply,norm_mul,norm_boundaryPoint,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (affineBlend_pos (A.radius_pos i) hR t)]

theorem outerPath_injective (hrot : A.rotation = 1) {R : ℝ}
    (hR : ∀ i, A.radius i < R) (i : Fin n) :
    Function.Injective (A.outerPath hrot R i) := by
  intro t u he
  have h := congrArg norm he
  rw [A.outerPath_norm hrot ((A.radius_pos i).trans (hR i)),
    A.outerPath_norm hrot ((A.radius_pos i).trans (hR i))] at h
  apply Subtype.ext
  dsimp [affineBlend] at h
  nlinarith [hR i]

theorem outerPath_norm_bounds (hrot : A.rotation = 1) {R : ℝ}
    (hR : ∀ i, A.radius i < R) (i : Fin n) (t : unitInterval) :
    A.radius i ≤ ‖A.outerPath hrot R i t‖ ∧ ‖A.outerPath hrot R i t‖ ≤ R := by
  rw [A.outerPath_norm hrot ((A.radius_pos i).trans (hR i))]
  have hp := mul_nonneg t.property.1 (sub_nonneg.mpr (hR i).le)
  have hq := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (hR i).le)
  dsimp [affineBlend]
  constructor <;> nlinarith

/-- Strictly ordered rays remain disjoint even though their initial radii vary. -/
theorem outerPaths_disjoint (hrot : A.rotation = 1) {R : ℝ} (hR : 0 < R) :
    Pairwise (fun i j => Disjoint (Set.range (A.outerPath hrot R i))
      (Set.range (A.outerPath hrot R j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨t,rfl⟩ ⟨u,hu⟩
  have hn := congrArg norm hu
  rw [A.outerPath_norm hrot hR,A.outerPath_norm hrot hR] at hn
  rw [A.outerPath_apply,A.outerPath_apply,hn] at hu
  have hz : ((affineBlend (A.radius i) R t : ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (affineBlend_pos (A.radius_pos i) hR t))
  have ha := mul_left_cancel₀ hz hu
  have he := boundaryPoint_inj_on_turn (A.angle_pos j) (A.angle_lt_one j)
    (A.angle_pos i) (A.angle_lt_one i) ha
  exact hij (A.angle_strictMono.injective he).symm

/-- A finite original global angle list gives actual ordered cap coordinates
in frame one at every sufficiently small positive common ribbon width. -/
theorem exists_outer_block_endpoints {r : ℕ} (hrot : A.rotation = 1)
    (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (horder : ∀ i k l, k < l → 0 < (d i l-d i k)*orientedArea (p i) (w i))
    (R : ℝ) (hR : ∀ i, ‖p i‖ < R) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : OrderedRayAngles (A.blockEndpoint w d ε),
        B.rotation = 1 ∧ (∀ q, B.radius q < R) := by
  obtain ⟨ε₁,hε₁,hsmall⟩ := A.exists_ordered_blockEndpoints_of_signed_area w d horder
  have hev : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ q : Fin (n*r), ‖A.blockEndpoint w d ε q‖ < R := by
    rw [Filter.eventually_all]
    intro q
    have hc : ContinuousAt (fun ε : ℝ => ‖A.blockEndpoint w d ε q‖) 0 := by
      unfold blockEndpoint
      fun_prop
    apply hc.eventually_lt continuousAt_const
    simpa [blockEndpoint] using hR (finProdFinEquiv.symm q).1
  obtain ⟨ε₂,hε₂,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro ε hε hεlt
  obtain ⟨B,hB⟩ := hsmall ε hε (hεlt.trans_le (min_le_left _ _))
  have hBrot : B.rotation = 1 := hB.trans hrot
  refine ⟨B,hBrot,?_⟩
  intro q
  rw [← B.norm_point_of_rotation_one hBrot q]
  apply hball
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε] using
    hεlt.trans_le (min_le_right ε₁ ε₂)

end OrderedRayAngles

/-- The original actual boundary angle list is used without rotating the
common exterior frame or changing its first label. -/
def globalOrderedRayAngles {n : ℕ} (α ρ : Fin n → ℝ)
    (hα : StrictMono α) (hα0 : ∀ i, 0 < α i) (hα1 : ∀ i, α i < 1)
    (hρ : ∀ i, 0 < ρ i) :
    OrderedRayAngles (fun i => (ρ i:ℂ)*boundaryPoint (α i)) where
  rotation := 1
  rotation_ne_zero := one_ne_zero
  angle := α
  angle_strictMono := hα
  angle_pos := hα0
  angle_lt_one := hα1
  radius := ρ
  radius_pos := hρ
  point_eq _ := by simp

end
end MatchgateWidth
