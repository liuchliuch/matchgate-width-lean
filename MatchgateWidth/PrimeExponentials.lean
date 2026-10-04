import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Preliminary facts for prime-square-root exponentials

These results formalize the monomial expansion and elementary algebraicity steps
in Lemma 6.1 of arXiv:2610.00079v1. The multiquadratic and Lindemann developments
are combined into the complete theorem in `IndependentPrimeExponentials.lean`.
-/

namespace MatchgateWidth

open scoped BigOperators

/-- The exponent obtained by expanding a monomial evaluated at exponentials. -/
def monomialExponent {ι : Type*} [Fintype ι] (z : ι → ℂ) (m : ι →₀ ℕ) : ℂ :=
  ∑ i, (m i : ℂ) * z i

/-- Multiplication of monomial values is addition of their exponents, including
for the constant monomial. -/
theorem exp_monomialExponent {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (m : ι →₀ ℕ) :
    Complex.exp (monomialExponent z m) = ∏ i, Complex.exp (z i) ^ m i := by
  simp only [monomialExponent, Complex.exp_sum, Complex.exp_nat_mul]

/-- The exact exponential-sum expansion of a rational polynomial. This is the
identity underlying the paper's expanded polynomial relation in Lemma 6.1. -/
theorem eval₂_exp_eq_sum {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (P : MvPolynomial ι ℚ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) (fun i => Complex.exp (z i)) P =
      ∑ m ∈ P.support, (P.coeff m : ℂ) * Complex.exp (monomialExponent z m) := by
  simp only [MvPolynomial.eval₂_eq', exp_monomialExponent]
  rfl

/-- A linearly independent family distinguishes natural-number monomial
exponents. This generic implication does not assert that prime square roots
satisfy its linear-independence hypothesis. -/
theorem monomialExponent_injective {ι : Type*} [Fintype ι]
    {z : ι → ℂ} (hz : LinearIndependent ℚ z) :
    Function.Injective (monomialExponent z) := by
  intro m n h
  have hq : ∀ i, (m i : ℚ) = (n i : ℚ) :=
    Fintype.linearIndependent_iffₛ.mp hz (fun i => (m i : ℚ)) (fun i => (n i : ℚ))
      (by simpa only [monomialExponent, Rat.smul_def, Rat.cast_natCast] using h)
  ext i
  exact_mod_cast hq i

/-- The positive real square root, considered as a complex number. -/
noncomputable def primeSquareRoot (p : ℕ) : ℂ := (Real.sqrt (p : ℝ) : ℂ)

@[simp] theorem primeSquareRoot_sq (p : ℕ) : primeSquareRoot p ^ 2 = (p : ℂ) := by
  simp only [primeSquareRoot, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p),
    Complex.ofReal_natCast]

/-- Algebraicity of each square root does not require primality. -/
theorem primeSquareRoot_isAlgebraic (p : ℕ) : IsAlgebraic ℚ (primeSquareRoot p) := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [primeSquareRoot_sq]
  exact isAlgebraic_natCast p

/-- All exponents in the polynomial expansion of prime-square-root
exponentials are algebraic. This includes the zero exponent. -/
theorem primeSquareRoot_monomialExponent_isAlgebraic
    {ι : Type*} [Fintype ι] (p : ι → ℕ) (m : ι →₀ ℕ) :
    IsAlgebraic ℚ (monomialExponent (fun i => primeSquareRoot (p i)) m) := by
  apply IsIntegral.isAlgebraic
  exact IsIntegral.sum _ (fun i _ =>
    (isIntegral_natCast (m i)).mul (primeSquareRoot_isAlgebraic (p i)).isIntegral)

end MatchgateWidth
