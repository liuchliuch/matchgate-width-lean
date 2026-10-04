import MatchgateWidth.PlanarDrawing
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Logarithmic separation of disk paths

The analytic tools for the disk crossing argument use the exponential covering
map. The domain is the contractible parameter square, not the graph drawing.
-/

namespace MatchgateWidth
noncomputable section
open Classical
open scoped ComplexConjugate

/-- A continuous nonvanishing complex function on the parameter square has a
continuous logarithm. This is obtained from the proved covering-space lifting
property, with contractibility supplying simple connectedness. -/
theorem exists_log_on_square (f : unitInterval × unitInterval → ℂ)
    (hf : Continuous f) (hne : ∀ x, f x ≠ 0) :
    ∃ L : unitInterval × unitInterval → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x) = f x := by
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨L, ⟨_, hL⟩, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨f, hf⟩ : C(unitInterval × unitInterval, ℂ))
    (a₀ := (0, 0)) (Complex.exp_log (hne (0, 0))) (by simpa using hne)
  exact ⟨L, L.continuous, fun x => congrFun hL x⟩

/-- A continuous logarithm whose exponential stays in a rotated open right
half-plane has a single, globally fixed integer branch along the interval. -/
theorem log_im_bounds_of_halfplane (L : unitInterval → ℂ) (hL : Continuous L)
    (θ : ℝ) (hpos : ∀ t, 0 < (Complex.exp (L t - θ * Complex.I)).re) :
    ∃ k : ℤ, ∀ t,
      θ - Real.pi / 2 + (k : ℝ) * (2 * Real.pi) < (L t).im ∧
      (L t).im < θ + Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by
  let T := fun t => L t - θ * Complex.I
  let Q := fun t => Complex.log (Complex.exp (T t))
  have hT : Continuous T := hL.sub continuous_const
  have hQ : Continuous Q := hT.cexp.clog (fun t =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (hpos t)))
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (Complex.exp_log (Complex.exp_ne_zero (T 0))).symm
  have hEq : T = fun t => Q t + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    apply Complex.isCoveringMap_exp.eq_of_comp_eq hT (hQ.add continuous_const) _ 0 hk
    funext t
    apply Subtype.ext
    change Complex.exp (T t) = Complex.exp (Q t + (k : ℂ) * (2 * Real.pi * Complex.I))
    exact (Complex.exp_log (Complex.exp_ne_zero (T t))).symm.trans
      (Complex.exp_eq_exp_iff_exists_int.mpr ⟨-k, by push_cast; ring⟩)
  refine ⟨k, fun t => ?_⟩
  have hb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos t)))
  have hi := congrArg Complex.im (congrFun hEq t)
  simp [T, Q, Complex.log_im] at hi
  constructor <;> linarith

/-- Strict convexity of the complex unit disk in the direction of `1`. -/
theorem re_lt_one_of_norm_le_one {z : ℂ} (hn : ‖z‖ ≤ 1) (hne : z ≠ 1) : z.re < 1 := by
  have hr := (Complex.re_le_norm z).trans hn
  apply lt_of_le_of_ne hr
  intro heq
  have him : z.im = 0 := by
    have hsq := Complex.sq_norm_sub_sq_re z
    have hnn := norm_nonneg z
    nlinarith [sq_nonneg z.im]
  exact hne (Complex.ext heq (by simpa using him))

/-- The difference from a boundary point toward any other disk point lies in
its rotated open right half-plane. -/
theorem boundary_sub_re_pos (θ : ℝ) {z : ℂ} (hn : ‖z‖ ≤ 1)
    (hne : z ≠ Complex.exp (θ * Complex.I)) :
    0 < ((Complex.exp (θ * Complex.I) - z) *
      Complex.exp (-(θ * Complex.I))).re := by
  have hnorm : ‖z * Complex.exp (-(θ * Complex.I))‖ ≤ 1 := by
    simpa [Complex.norm_exp] using hn
  have hneq : z * Complex.exp (-(θ * Complex.I)) ≠ 1 := by
    intro h
    apply hne
    have hh := congrArg (fun w => w * Complex.exp (θ * Complex.I)) h
    simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      mul_one, one_mul] using hh
  have hlt := re_lt_one_of_norm_le_one hnorm hneq
  rw [sub_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, Complex.sub_re,
    Complex.one_re]
  linarith

/-- Integer branch compatibility at a corner with increasing circle angles. -/
theorem branch_eq_sub_one_of_order {a b x : ℝ} {m k : ℤ}
    (hab : a < b) (hba : b < a + 2 * Real.pi)
    (hm : a - Real.pi / 2 + (m : ℝ) * (2 * Real.pi) < x ∧
      x < a + Real.pi / 2 + (m : ℝ) * (2 * Real.pi))
    (hk : b + Real.pi - Real.pi / 2 + (k : ℝ) * (2 * Real.pi) < x ∧
      x < b + Real.pi + Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) : k = m - 1 := by
  have h₁ : (k : ℝ) - m < 0 := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    nlinarith
  have h₂ : -2 < (k : ℝ) - m := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    nlinarith
  have hi₁ : k - m < 0 := by exact_mod_cast h₁
  have hi₂ : -2 < k - m := by exact_mod_cast h₂
  omega

/-- Integer branch compatibility when the first angle follows the second. -/
theorem branch_eq_of_reverse_order {a b x : ℝ} {m k : ℤ}
    (hba : b < a) (hab : a < b + 2 * Real.pi)
    (hm : a - Real.pi / 2 + (m : ℝ) * (2 * Real.pi) < x ∧
      x < a + Real.pi / 2 + (m : ℝ) * (2 * Real.pi))
    (hk : b + Real.pi - Real.pi / 2 + (k : ℝ) * (2 * Real.pi) < x ∧
      x < b + Real.pi + Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) : k = m := by
  have h₁ : (k : ℝ) - m < 1 := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    nlinarith
  have h₂ : -1 < (k : ℝ) - m := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    nlinarith
  have hi₁ : k - m < 1 := by exact_mod_cast h₁
  have hi₂ : -1 < k - m := by exact_mod_cast h₂
  omega

/-- Rotating the tangent half-plane by one additional half-turn reverses its
sign. -/
theorem exp_neg_add_pi_mul_I (θ : ℝ) :
    Complex.exp (-((θ + Real.pi : ℝ) * Complex.I)) =
      -Complex.exp (-(θ * Complex.I)) := by
  have he : -((θ + Real.pi : ℝ) * Complex.I) =
      -(θ * Complex.I) + -(Real.pi * Complex.I) := by push_cast; ring
  rw [he, Complex.exp_add]
  simp

/-- Two continuous paths in the closed unit disk whose four endpoint angles
strictly alternate must intersect. The proof uses exponential covering-space
lifting and four tangent half-plane constraints, with no Jordan-curve axiom. -/
theorem disk_paths_cross_radians {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + 2 * Real.pi)
    (γ : Path (Complex.exp (a * Complex.I)) (Complex.exp (c * Complex.I)))
    (δ : Path (Complex.exp (b * Complex.I)) (Complex.exp (d * Complex.I)))
    (hγ : ∀ u, ‖γ u‖ ≤ 1) (hδ : ∀ u, ‖δ u‖ ≤ 1) :
    ∃ u v, γ u = δ v := by
  by_contra hcross
  have hne : ∀ u v, γ u ≠ δ v := by simpa only [not_exists] using hcross
  let f := fun x : unitInterval × unitInterval => γ x.1 - δ x.2
  have hf : Continuous f := (γ.continuous.comp continuous_fst).sub
    (δ.continuous.comp continuous_snd)
  obtain ⟨L, hL, hLf⟩ := exists_log_on_square f hf (fun x => sub_ne_zero.mpr (hne x.1 x.2))
  have rot (x : unitInterval × unitInterval) (θ : ℝ) :
      Complex.exp (L x - θ * Complex.I) =
        (γ x.1 - δ x.2) * Complex.exp (-(θ * Complex.I)) := by
    rw [Complex.exp_sub, hLf, div_eq_mul_inv, ← Complex.exp_neg]
  have leftPos (u : unitInterval) : 0 < (Complex.exp (L (0, u) - a * Complex.I)).re := by
    rw [rot, Path.source]
    exact boundary_sub_re_pos a (hδ u) (by simpa only [Path.source] using (hne 0 u).symm)
  have rightPos (u : unitInterval) : 0 < (Complex.exp (L (1, u) - c * Complex.I)).re := by
    rw [rot, Path.target]
    exact boundary_sub_re_pos c (hδ u) (by simpa only [Path.target] using (hne 1 u).symm)
  have bottomPos (u : unitInterval) :
      0 < (Complex.exp (L (u, 0) - (b + Real.pi : ℝ) * Complex.I)).re := by
    rw [rot, Path.source, exp_neg_add_pi_mul_I]
    have he : (γ u - Complex.exp (b * Complex.I)) * -Complex.exp (-(b * Complex.I)) =
        (Complex.exp (b * Complex.I) - γ u) * Complex.exp (-(b * Complex.I)) := by ring
    rw [he]
    exact boundary_sub_re_pos b (hγ u) (by simpa only [Path.source] using hne u 0)
  have topPos (u : unitInterval) :
      0 < (Complex.exp (L (u, 1) - (d + Real.pi : ℝ) * Complex.I)).re := by
    rw [rot, Path.target, exp_neg_add_pi_mul_I]
    have he : (γ u - Complex.exp (d * Complex.I)) * -Complex.exp (-(d * Complex.I)) =
        (Complex.exp (d * Complex.I) - γ u) * Complex.exp (-(d * Complex.I)) := by ring
    rw [he]
    exact boundary_sub_re_pos d (hγ u) (by simpa only [Path.target] using hne u 1)
  obtain ⟨i, hi⟩ := log_im_bounds_of_halfplane (fun u => L (0, u))
    (hL.comp (continuous_const.prodMk continuous_id)) a leftPos
  obtain ⟨j, hj⟩ := log_im_bounds_of_halfplane (fun u => L (1, u))
    (hL.comp (continuous_const.prodMk continuous_id)) c rightPos
  obtain ⟨k, hk⟩ := log_im_bounds_of_halfplane (fun u => L (u, 0))
    (hL.comp (continuous_id.prodMk continuous_const)) (b + Real.pi) bottomPos
  obtain ⟨l, hl⟩ := log_im_bounds_of_halfplane (fun u => L (u, 1))
    (hL.comp (continuous_id.prodMk continuous_const)) (d + Real.pi) topPos
  have hki : k = i - 1 := branch_eq_sub_one_of_order hab (by linarith) (hi 0) (hk 0)
  have hkj : k = j := branch_eq_of_reverse_order hbc (by linarith) (hj 0) (hk 1)
  have hlj : l = j - 1 := branch_eq_sub_one_of_order hcd (by linarith) (hj 1) (hl 1)
  have hli : l = i - 1 := branch_eq_sub_one_of_order (by linarith) hda (hi 1) (hl 0)
  omega

end
end MatchgateWidth
