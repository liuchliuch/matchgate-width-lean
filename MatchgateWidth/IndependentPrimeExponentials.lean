import MatchgateWidth.PrimeRootIndependence
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic independence of prime-square-root exponentials

This is the full independence statement of Lemma 6.1: exponentials of square
roots of distinct primes are algebraically independent over the rationals.
The proof expands a polynomial into distinct exponential monomials and applies
the established integral-exponent Lindemann--Weierstrass theorem.
-/

noncomputable section
namespace MatchgateWidth
open scoped BigOperators

/-- Monomial exponents built from prime square roots are algebraic integers. -/
theorem primeSquareRoot_monomialExponent_isIntegral
    {ι : Type*} [Fintype ι] (p : ι → ℕ) (m : ι →₀ ℕ) :
    IsIntegral ℤ (monomialExponent (fun i => primeSquareRoot (p i)) m) := by
  exact IsIntegral.sum _ (fun i _ =>
    (isIntegral_natCast (m i)).mul (primeSquareRoot_isIntegral (p i)))

/-- The exponential monomials in distinct prime square roots are rationally
linearly independent. -/
theorem linearIndependent_primeExponentialMonomials
    {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    LinearIndependent ℚ (fun m : ι →₀ ℕ =>
      Complex.exp (monomialExponent (fun i => primeSquareRoot (p i)) m)) := by
  exact LindemannAlgebraicPart.linearIndependent_exp_integral _
    (monomialExponent_injective (linearIndependent_primeSquareRoot p hp hinj))
    (primeSquareRoot_monomialExponent_isIntegral p)

/-- Lemma 6.1 for a finite family of distinct primes. -/
theorem algebraicIndependent_primeExponentials_finite
    {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    AlgebraicIndependent ℚ (fun i => Complex.exp (primeSquareRoot (p i))) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  have hrel : ∑ m ∈ P.support, (P.coeff m : ℂ) *
      Complex.exp (monomialExponent (fun i => primeSquareRoot (p i)) m) = 0 := by
    rw [← eval₂_exp_eq_sum]
    exact hP
  have hz := linearIndependent_iff'.mp (linearIndependent_primeExponentialMonomials p hp hinj)
    P.support P.coeff (by simpa only [Rat.smul_def] using hrel)
  apply MvPolynomial.ext
  intro m
  by_cases hm : m ∈ P.support
  · simpa using hz m hm
  · simpa using MvPolynomial.notMem_support_iff.mp hm

/-- Lemma 6.1, without a finiteness restriction on the family of distinct primes. -/
theorem algebraicIndependent_primeExponentials
    {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    AlgebraicIndependent ℚ (fun i => Complex.exp (primeSquareRoot (p i))) := by
  apply algebraicIndependent_of_finite_type
  intro s hs
  let := hs.fintype
  exact algebraicIndependent_primeExponentials_finite (fun i : s => p i)
    (fun i => hp i) (hinj.comp Subtype.val_injective)

/-- Real-valued version of Lemma 6.1, with the paper's exact positive square roots. -/
theorem algebraicIndependent_real_primeExponentials
    {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    AlgebraicIndependent ℚ (fun i => Real.exp (Real.sqrt (p i : ℝ))) := by
  apply (IsScalarTower.toAlgHom ℚ ℝ ℂ).algebraicIndependent_iff
    (RingHom.injective _ ) |>.mp
  change AlgebraicIndependent ℚ (fun i => (Real.exp (Real.sqrt (p i : ℝ)) : ℂ))
  simpa only [Complex.ofReal_exp, primeSquareRoot] using
    algebraicIndependent_primeExponentials p hp hinj

end MatchgateWidth
