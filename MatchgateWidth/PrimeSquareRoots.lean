import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Distinct prime square classes

The product of powers of distinct primes is a square exactly when all exponents
are even. In particular, a product with binary exponents represents the trivial
square class over `ℚ` only when every exponent is zero.

This is the elementary arithmetic input to the paper's multiquadratic argument.
It does not assert linear independence of real square roots or
Lindemann–Weierstrass algebraic independence.
-/

namespace MatchgateWidth

variable {ι : Type*}

/-- The multiplicity of a selected prime in a product of powers of distinct primes. -/
theorem primePowerProduct_factorization (s : Finset ι) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {i : ι} (hi : i ∈ s) :
    (∏ j ∈ s, p j ^ e j).factorization (p i) = e i := by
  classical
  rw [Nat.factorization_prod_apply (fun j _ ↦ pow_ne_zero _ (hp j).ne_zero)]
  simp only [(hp _).factorization_pow, Finsupp.single_apply, hinj.eq_iff]
  simp [hi]

/-- Products of powers of distinct primes are squares precisely for even exponents. -/
theorem isSquare_primePowerProduct_iff (s : Finset ι) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    IsSquare (∏ i ∈ s, p i ^ e i) ↔ ∀ i ∈ s, Even (e i) := by
  constructor
  · intro h i hi
    have he := Nat.isSquare_iff_even_factorization.mp h (p i) (hp i)
    rwa [primePowerProduct_factorization s p e hp hinj hi] at he
  · intro he
    apply Finset.isSquare_prod
    intro i hi
    obtain ⟨k, hk⟩ := he i hi
    exact ⟨p i ^ k, by rw [hk, pow_add]⟩

/-- The same parity criterion holds for the rational square class. -/
theorem isSquare_rat_primePowerProduct_iff (s : Finset ι) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    IsSquare (∏ i ∈ s, (p i : ℚ) ^ e i) ↔ ∀ i ∈ s, Even (e i) := by
  simp only [← Nat.cast_pow, ← Nat.cast_prod, Rat.isSquare_natCast_iff]
  exact isSquare_primePowerProduct_iff s p e hp hinj

/-- A binary-exponent product is a rational square only for the empty selection. -/
theorem isSquare_rat_primeBinaryProduct_iff (s : Finset ι) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (he : ∀ i ∈ s, e i ≤ 1) :
    IsSquare (∏ i ∈ s, (p i : ℚ) ^ e i) ↔ ∀ i ∈ s, e i = 0 := by
  rw [isSquare_rat_primePowerProduct_iff s p e hp hinj]
  constructor
  · intro h i hi
    obtain ⟨k, hk⟩ := h i hi
    have := he i hi
    omega
  · intro h i hi
    rw [h i hi]
    exact ⟨0, rfl⟩

/-- No nonempty subset of distinct primes has square product in `ℚ`. -/
theorem isSquare_rat_primeProduct_iff (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    IsSquare (∏ i ∈ s, (p i : ℚ)) ↔ s = ∅ := by
  classical
  simpa only [pow_one, Nat.one_ne_zero, imp_false, Finset.eq_empty_iff_forall_notMem]
    using isSquare_rat_primeBinaryProduct_iff s p (fun _ ↦ 1) hp hinj
      (fun _ _ ↦ le_rfl)

/-- Equivalent natural-number version of the nonempty-subset criterion. -/
theorem isSquare_primeProduct_iff (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    IsSquare (∏ i ∈ s, p i) ↔ s = ∅ := by
  rw [← Rat.isSquare_natCast_iff, Nat.cast_prod]
  exact isSquare_rat_primeProduct_iff s p hp hinj

end MatchgateWidth
