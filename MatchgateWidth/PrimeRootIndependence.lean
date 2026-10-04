import MatchgateWidth.PrimeSquareRoots
import MatchgateWidth.PrimeExponentials
import MatchgateWidth.LindemannIntegralExponentials
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Rational linear independence of distinct prime square roots

Square roots in a finite Galois extension transform by sign characters. Distinct
rational square classes give distinct characters, and Dedekind independence of
characters then gives linear independence of the roots. This avoids assuming
any multiquadratic automorphisms or degree computation.
-/

noncomputable section
namespace MatchgateWidth
open scoped BigOperators

section SignCharacter
variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem quadratic_map_eq_or_eq_neg (x : K) (a : ℚ)
    (hx : x ^ 2 = algebraMap ℚ K a) (σ : K ≃ₐ[ℚ] K) :
    σ x = x ∨ σ x = -x := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [← map_pow, hx, AlgEquiv.commutes]

/-- The sign character associated with a nonzero square root of a rational. -/
private def quadraticCharacter (x : K) (a : ℚ) (hx0 : x ≠ 0)
    (hx : x ^ 2 = algebraMap ℚ K a) : (K ≃ₐ[ℚ] K) →* K where
  toFun σ := σ x / x
  map_one' := by simp [hx0]
  map_mul' σ τ := by
    rcases quadratic_map_eq_or_eq_neg x a hx τ with hτ | hτ <;>
      simp [AlgEquiv.mul_apply, hτ, hx0, neg_div, mul_neg]

private theorem quadraticCharacter_injective {ι : Type*}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (x : ι → K) (a : ι → ℚ) (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ K (a i))
    (ha : ∀ i j, i ≠ j → ¬IsSquare (a i * a j)) :
    Function.Injective (fun i => quadraticCharacter (x i) (a i) (hx0 i) (hx i)) := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  intro i j hij
  by_contra hne
  have hfixed : ∀ σ : K ≃ₐ[ℚ] K, σ (x i * x j) = x i * x j := by
    intro σ
    have hc : σ (x i) / x i = σ (x j) / x j :=
      congrArg (fun c : (K ≃ₐ[ℚ] K) →* K => c σ) hij
    rcases quadratic_map_eq_or_eq_neg (x i) (a i) (hx i) σ with hi | hi <;>
      rcases quadratic_map_eq_or_eq_neg (x j) (a j) (hx j) σ with hj | hj
    · simp [hi, hj]
    · norm_num [hi, hj, hx0] at hc
    · norm_num [hi, hj, hx0] at hc
    · simp [hi, hj]
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (x i * x j)).mpr hfixed
  apply ha i j hne
  refine ⟨q, ?_⟩
  apply (algebraMap ℚ K).injective
  rw [map_mul, ← sq, map_pow, hq, mul_pow, hx i, hx j]

/-- Square roots of pairwise distinct rational square classes are independent
in a finite Galois extension. -/
theorem linearIndependent_quadratic_roots
    {ι : Type*} [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (x : ι → K) (a : ι → ℚ) (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ K (a i))
    (ha : ∀ i j, i ≠ j → ¬IsSquare (a i * a j)) :
    LinearIndependent ℚ x := by
  classical
  let c := fun i => quadraticCharacter (x i) (a i) (hx0 i) (hx i)
  have hc : LinearIndependent K (fun i => (c i : (K ≃ₐ[ℚ] K) → K)) :=
    (linearIndependent_monoidHom (K ≃ₐ[ℚ] K) K).comp c
      (quadraticCharacter_injective x a hx0 hx ha)
  rw [linearIndependent_iff'] at hc ⊢
  intro s b hb i hi
  have hsum : ∑ j ∈ s, (algebraMap ℚ K (b j) * x j) •
      (c j : (K ≃ₐ[ℚ] K) → K) = 0 := by
    ext σ
    have hσ := congrArg σ hb
    simp only [map_sum, map_smul, map_zero] at hσ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      c, quadraticCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
    convert hσ using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Algebra.smul_def]
    field_simp [hx0]

  have hz := hc s (fun j => algebraMap ℚ K (b j) * x j) hsum i hi
  exact (algebraMap ℚ K).injective (by simpa [hx0 i] using hz)

end SignCharacter
/-- Each prime square root is an algebraic integer, independently of primality. -/
theorem primeSquareRoot_isIntegral (p : ℕ) : IsIntegral ℤ (primeSquareRoot p) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [primeSquareRoot_sq]
  exact isIntegral_natCast p

private theorem primeSquareRoot_ne_zero {p : ℕ} (hp : p.Prime) :
    primeSquareRoot p ≠ 0 := by
  intro h
  have hs := primeSquareRoot_sq p
  rw [h, zero_pow (by decide)] at hs
  exact hp.ne_zero (by exact_mod_cast hs.symm)

private theorem linearIndependent_primeSquareRoot_finite
    {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    LinearIndependent ℚ (fun i => primeSquareRoot (p i)) := by
  classical
  obtain ⟨K, hfin, hgal, hK⟩ :=
    LindemannAlgebraicPart.exists_finite_galois_field
      (fun i => primeSquareRoot (p i)) (fun i => (primeSquareRoot_isIntegral (p i)).tower_top)
  let : FiniteDimensional ℚ K := hfin
  let : IsGalois ℚ K := hgal
  let x : ι → K := fun i => ⟨primeSquareRoot (p i), hK i⟩
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i hi
    exact primeSquareRoot_ne_zero (hp i) (congrArg Subtype.val hi)
  have hx : ∀ i, x i ^ 2 = algebraMap ℚ K (p i : ℚ) := by
    intro i
    apply Subtype.ext
    simp [x]
  have ha : ∀ i j, i ≠ j → ¬IsSquare ((p i : ℚ) * (p j : ℚ)) := by
    intro i j hij hsq
    have hs : IsSquare (∏ k ∈ ({i, j} : Finset ι), (p k : ℚ)) := by
      simpa [hij] using hsq
    have he := (isSquare_rat_primeProduct_iff {i, j} p hp hinj).mp hs
    simp at he
  have hli := linearIndependent_quadratic_roots x (fun i => (p i : ℚ)) hx0 hx ha
  exact hli.map' K.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

/-- The positive complex square roots of any family of distinct primes are
linearly independent over the rationals. -/
theorem linearIndependent_primeSquareRoot
    {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    LinearIndependent ℚ (fun i => primeSquareRoot (p i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_primeSquareRoot_finite (fun i : s => p i)
    (fun i => hp i) (hinj.comp Subtype.val_injective)

end MatchgateWidth
