import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Group.UniqueProds.VectorSpace

noncomputable section
namespace MatchgateWidth.LindemannAlgebraicPart
open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A Galois-fixed algebraic integer in a finite Galois extension of the rationals
is an ordinary integer. -/
theorem exists_intCast_of_integral_fixed
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {x : K} (hx : IsIntegral ℤ x)
    (hfixed : ∀ σ : K ≃ₐ[ℚ] K, σ x = x) :
    ∃ z : ℤ, (z : K) = x := by
  obtain ⟨q, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfixed
  have hq : IsIntegral ℤ q := isIntegral_algebraMap_iff.mp hx
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  exact ⟨z, by simp [← hz]⟩

/-- Formal exponential polynomials with integer coefficients. -/
abbrev ExpPoly (K : Type*) := AddMonoidAlgebra ℤ K

/-- Apply a field automorphism to the formal exponents. -/
def conjugate (σ : K ≃ₐ[ℚ] K) : ExpPoly K ≃+* ExpPoly K :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ σ.toAddEquiv

@[simp] theorem conjugate_coeff (σ : K ≃ₐ[ℚ] K) (u : ExpPoly K) (x : K) :
    (conjugate σ u).coeff x = u.coeff (σ.symm x) := by
  simp [conjugate]

@[simp] theorem conjugate_one (u : ExpPoly K) : conjugate (1 : K ≃ₐ[ℚ] K) u = u := by
  ext x
  simp only [conjugate_coeff]
  rfl

@[simp] theorem conjugate_mul_apply (σ τ : K ≃ₐ[ℚ] K) (u : ExpPoly K) :
    conjugate σ (conjugate τ u) = conjugate (σ * τ) u := by
  ext x
  simp only [conjugate_coeff]
  rfl

/-- A finite product over all Galois conjugates, in the formal exponential ring. -/
def galoisProduct [Fintype (K ≃ₐ[ℚ] K)] (u : ExpPoly K) : ExpPoly K :=
  ∏ σ : K ≃ₐ[ℚ] K, conjugate σ u

theorem galoisProduct_ne_zero [Fintype (K ≃ₐ[ℚ] K)] {u : ExpPoly K} (hu : u ≠ 0) :
    galoisProduct u ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun σ _ => fun h => hu ((conjugate σ).map_eq_zero_iff.mp h))

@[simp] theorem conjugate_galoisProduct [Fintype (K ≃ₐ[ℚ] K)]
    (σ : K ≃ₐ[ℚ] K) (u : ExpPoly K) :
    conjugate σ (galoisProduct u) = galoisProduct u := by
  classical
  simp only [galoisProduct, map_prod, conjugate_mul_apply]
  exact Equiv.prod_comp (Equiv.mulLeft σ) (fun τ => conjugate τ u)

/-- Reverse all formal exponents. -/
def reverseExponents : ExpPoly K ≃+* ExpPoly K :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (AddEquiv.neg K)

@[simp] theorem reverseExponents_coeff (u : ExpPoly K) (x : K) :
    (reverseExponents u).coeff x = u.coeff (-x) := by
  simp [reverseExponents]

@[simp] theorem conjugate_reverseExponents (σ : K ≃ₐ[ℚ] K) (u : ExpPoly K) :
    conjugate σ (reverseExponents u) = reverseExponents (conjugate σ u) := by
  ext x
  simp

/-- Multiplication by the reversed polynomial makes the constant coefficient a
sum of squares. This removes the possible vanishing of the constant coefficient
in the first Galois product. -/
theorem mul_reverseExponents_coeff_zero (u : ExpPoly K) :
    (u * reverseExponents u).coeff 0 = ∑ x ∈ u.coeff.support, u.coeff x ^ 2 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp [Finsupp.sum, pow_two]

theorem mul_reverseExponents_coeff_zero_pos {u : ExpPoly K} (hu : u ≠ 0) :
    0 < (u * reverseExponents u).coeff 0 := by
  classical
  rw [mul_reverseExponents_coeff_zero]
  apply Finset.sum_pos'
  · intro x hx
    exact sq_nonneg _
  · have hc : u.coeff ≠ 0 := by simpa using hu
    obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr hc
    exact ⟨x, hx, sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)⟩

/-- All exponents occurring with nonzero coefficients are algebraic integers. -/
def IntegralSupport (u : ExpPoly K) : Prop :=
  ∀ x ∈ u.coeff.support, IsIntegral ℤ x

theorem IntegralSupport.one : IntegralSupport (1 : ExpPoly K) := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  exact isIntegral_zero

theorem IntegralSupport.mul {u v : ExpPoly K}
    (hu : IntegralSupport u) (hv : IntegralSupport v) : IntegralSupport (u * v) := by
  classical
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset u v hx)
  exact (hu y hy).add (hv z hz)

theorem IntegralSupport.conjugate {u : ExpPoly K} (hu : IntegralSupport u)
    (σ : K ≃ₐ[ℚ] K) : IntegralSupport (conjugate σ u) := by
  intro x hx
  have hx' : σ.symm x ∈ u.coeff.support := by
    simpa only [Finsupp.mem_support_iff, conjugate_coeff] using hx
  simpa using map_isIntegral_int σ.toRingHom (hu _ hx')

theorem IntegralSupport.galoisProduct [Fintype (K ≃ₐ[ℚ] K)]
    {u : ExpPoly K} (hu : IntegralSupport u) : IntegralSupport (galoisProduct u) := by
  classical
  unfold MatchgateWidth.LindemannAlgebraicPart.galoisProduct
  exact Finset.prod_induction _ _ (fun _ _ => IntegralSupport.mul)
    IntegralSupport.one (fun σ _ => hu.conjugate σ)

theorem IntegralSupport.reverseExponents {u : ExpPoly K} (hu : IntegralSupport u) :
    IntegralSupport (reverseExponents u) := by
  intro x hx
  have hx' : -x ∈ u.coeff.support := by
    simpa only [Finsupp.mem_support_iff, reverseExponents_coeff] using hx
  simpa using (hu _ hx').neg

/-- A polynomial evaluated at an algebraic integer is again an algebraic integer. -/
theorem integral_aeval {x : K} (hx : IsIntegral ℤ x) (g : ℤ[X]) :
    IsIntegral ℤ (aeval x g) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n z =>
    simpa [aeval_monomial] using (isIntegral_intCast z).mul (hx.pow n)

theorem IntegralSupport.zero : IntegralSupport (0 : ExpPoly K) := by
  simp [IntegralSupport]

theorem IntegralSupport.add {u v : ExpPoly K}
    (hu : IntegralSupport u) (hv : IntegralSupport v) : IntegralSupport (u + v) := by
  intro x hx
  have hx' : u.coeff x + v.coeff x ≠ 0 := by simpa using hx
  by_cases hux : u.coeff x = 0
  · exact hv x (Finsupp.mem_support_iff.mpr (by simpa [hux] using hx'))
  · exact hu x (Finsupp.mem_support_iff.mpr hux)

theorem IntegralSupport.single {x : K} (hx : IsIntegral ℤ x) (z : ℤ) :
    IntegralSupport (AddMonoidAlgebra.single x z) := by
  intro y hy
  have hy' : y = x := Finset.mem_singleton.mp (Finsupp.support_single_subset hy)
  subst y
  exact hx

theorem IntegralSupport.sum {ι : Type*} (s : Finset ι) (u : ι → ExpPoly K)
    (hu : ∀ i ∈ s, IntegralSupport (u i)) : IntegralSupport (∑ i ∈ s, u i) := by
  classical
  exact Finset.sum_induction _ _ (fun _ _ => IntegralSupport.add)
    IntegralSupport.zero hu

/-- The polynomial moment of a formal exponential polynomial. -/
def moment (u : ExpPoly K) (g : ℤ[X]) : K :=
  u.coeff.sum (fun x b => (b : K) * aeval x g)

theorem moment_isIntegral {u : ExpPoly K} (hu : IntegralSupport u) (g : ℤ[X]) :
    IsIntegral ℤ (moment u g) := by
  apply IsIntegral.sum
  intro x hx
  exact (isIntegral_intCast _).mul (integral_aeval (hu x hx) g)

theorem moment_conjugate (σ : K ≃ₐ[ℚ] K) (u : ExpPoly K) (g : ℤ[X]) :
    moment (conjugate σ u) g = σ (moment u g) := by
  classical
  unfold moment
  rw [conjugate, AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.sum_equivMapDomain]
  simp only [Finsupp.sum, map_sum, map_mul, map_intCast]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | monomial n z => simp [aeval_monomial]

/-- Galois-invariant formal exponential polynomials supported on algebraic
integers have integer polynomial moments. -/
theorem moment_eq_intCast [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {u : ExpPoly K} (hu : IntegralSupport u)
    (hinv : ∀ σ : K ≃ₐ[ℚ] K, conjugate σ u = u) (g : ℤ[X]) :
    ∃ z : ℤ, (z : K) = moment u g := by
  apply exists_intCast_of_integral_fixed (moment_isIntegral hu g)
  intro σ
  rw [← moment_conjugate, hinv]

end MatchgateWidth.LindemannAlgebraicPart
