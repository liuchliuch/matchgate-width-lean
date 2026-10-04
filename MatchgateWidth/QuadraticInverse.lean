import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Inverses and homogeneous quadratic matrix equations

Finite-dimensional algebra lemma for a future exact matchgate-matrix inverse
argument. No matchgate composition or inverse-closure assertion is assumed.
-/

namespace MatchgateWidth

noncomputable section

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- In a finite-dimensional algebra, a left inverse lies in the linear span of
nonnegative powers. This is proved by invariant finite-dimensional linear maps. -/
theorem inverse_mem_span_nonnegative_powers (a b : A) (hba : b * a = 1) :
    b ∈ Submodule.span K (Set.range (fun n : ℕ => a ^ n)) := by
  let W : Submodule K A := Submodule.span K (Set.range (fun n : ℕ => a ^ n))
  have hstable : ∀ x ∈ W, a * x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨n + 1, pow_succ' a n⟩
    | zero => simpa using W.zero_mem
    | add x y hx hy ihx ihy => simpa [mul_add] using W.add_mem ihx ihy
    | smul c x hx ih => simpa [mul_smul_comm] using W.smul_mem c ih
  let L : W →ₗ[K] W := (LinearMap.mulLeft K a).restrict hstable
  have hinj : Function.Injective L := by
    intro x y h
    apply Subtype.ext
    have hv : a * (x : A) = a * (y : A) := congrArg Subtype.val h
    have hb := congrArg (fun z => b * z) hv
    simpa only [← mul_assoc, hba, one_mul] using hb
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  have h1 : (1 : A) ∈ W := Submodule.subset_span ⟨0, pow_zero a⟩
  obtain ⟨w, hw⟩ := hsurj ⟨1, h1⟩
  have haw : a * (w : A) = 1 := congrArg Subtype.val hw
  have hbw : b = (w : A) := by
    calc
      b = b * 1 := (mul_one b).symm
      _ = b * (a * (w : A)) := by rw [haw]
      _ = (w : A) := by rw [← mul_assoc, hba, one_mul]
  rw [hbw]
  exact w.property

/-- A linear equation true on every nonnegative power is true on the inverse. -/
theorem linear_equation_inverse_of_powers (a b : A) (hba : b * a = 1)
    (L : A →ₗ[K] K) (h : ∀ n : ℕ, L (a ^ n) = 0) : L b = 0 := by
  have hs : Submodule.span K (Set.range (fun n : ℕ => a ^ n)) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    exact h n
  exact hs (inverse_mem_span_nonnegative_powers a b hba)

section Matrices

open scoped Kronecker
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Tensor-square powers are the tensor squares of powers. -/
theorem matrix_tensorSquare_pow (P : Matrix n n K) (m : ℕ) :
    (P ⊗ₖ P) ^ m = (P ^ m) ⊗ₖ (P ^ m) := by
  induction m with
  | zero => simp []
  | succ m ih =>
    simp only [pow_succ, ih, Matrix.mul_kronecker_mul]

/-- Every homogeneous quadratic matrix equation holding on all powers holds on
the inverse. A linear functional of the tensor square is exactly such an equation. -/
theorem quadratic_equation_inverse_of_powers (P D : Matrix n n K)
    (hDP : D * P = 1)
    (L : Matrix (n × n) (n × n) K →ₗ[K] K)
    (h : ∀ m : ℕ, L ((P ^ m) ⊗ₖ (P ^ m)) = 0) : L (D ⊗ₖ D) = 0 := by
  have hi : (D ⊗ₖ D) * (P ⊗ₖ P) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hDP, Matrix.one_kronecker_one]
  apply linear_equation_inverse_of_powers (P ⊗ₖ P) (D ⊗ₖ D) hi L
  intro m
  rw [matrix_tensorSquare_pow]
  exact h m

end Matrices
end
end MatchgateWidth
