import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Prime.Infinite
import MatchgateWidth.LindemannGaloisHelpers

/-!
# Arithmetic completion of the exponential approximation estimate

The approximation theorem in mathlib is converted here into the contradiction
used in the algebraic part of Lindemann--Weierstrass. The condition on polynomial
moments is explicit: it is supplied by Galois invariance and integrality in the
classical argument, not by any transcendence assumption.
-/

noncomputable section

namespace MatchgateWidth.LindemannAlgebraicPart

open scoped BigOperators Nat
open Polynomial Filter Topology

/-- A nonzero integer has complex norm at least one. -/
theorem one_le_norm_intCast {a : ℤ} (ha : a ≠ 0) : 1 ≤ ‖(a : ℂ)‖ := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast (Int.one_le_abs ha)

/-- The arithmetic--analytic contradiction underlying Lindemann--Weierstrass.
The nonzero exponents are roots of one integer polynomial with nonzero constant
term. Their integer-weighted polynomial moments are integers. Under exactly
these arithmetic conditions, their exponential sum cannot be a nonzero integer.
-/
theorem exp_sum_ne_zero_of_integer_moments
    {ι : Type*} [Fintype ι] (r : ι → ℂ) (b : ι → ℤ)
    (f : ℤ[X]) (hf : f.eval 0 ≠ 0)
    (hr : ∀ i, r i ∈ f.aroots ℂ)
    (hm : ∀ g : ℤ[X], ∃ z : ℤ, (z : ℂ) = ∑ i, (b i : ℂ) * aeval (r i) g)
    (a : ℤ) (ha : a ≠ 0) :
    (a : ℂ) + ∑ i, (b i : ℂ) * Complex.exp (r i) ≠ 0 := by
  classical
  intro hrel
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf
  let B : ℝ := ∑ i, ‖(b i : ℂ)‖
  have hdecay := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop B c 1
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes
    (max N (max (f.eval 0).natAbs a.natAbs + 1))
  have hpf : (f.eval 0).natAbs < p := by omega
  have hpa : a.natAbs < p := by omega
  have hpN : N ≤ p := by omega
  obtain ⟨n, hnp, g, _, hg⟩ := hc p hpf hp
  obtain ⟨z, hz⟩ := hm g
  have hap : ¬ (p : ℤ) ∣ a := by
    intro h
    exact (not_le_of_gt hpa) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (Int.natCast_dvd.mp h))
  have hnonzero : n * a + (p : ℤ) * z ≠ 0 := by
    intro hzero
    have hdiv : (p : ℤ) ∣ n * a := by
      apply (dvd_add_left (dvd_mul_right (p : ℤ) z)).mp
      rw [hzero]
      exact dvd_zero _
    exact (Int.Prime.dvd_mul' hp hdiv).elim hnp hap
  have hidentity :
      ∑ i, (b i : ℂ) * (n • Complex.exp (r i) - p • aeval (r i) g) =
        -((n * a + (p : ℤ) * z : ℤ) : ℂ) := by
    simp only [zsmul_eq_mul, nsmul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    simp_rw [mul_left_comm (b _ : ℂ)]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hz]
    have heq : ∑ i, (b i : ℂ) * Complex.exp (r i) = -(a : ℂ) := by
      linear_combination hrel
    rw [heq]
    push_cast
    ring
  have hbound : ‖((n * a + (p : ℤ) * z : ℤ) : ℂ)‖ ≤ B * c ^ p / (p - 1)! := by
    calc
      ‖((n * a + (p : ℤ) * z : ℤ) : ℂ)‖ =
          ‖∑ i, (b i : ℂ) * (n • Complex.exp (r i) - p • aeval (r i) g)‖ := by
            rw [hidentity, norm_neg]
      _ ≤ ∑ i, ‖(b i : ℂ) * (n • Complex.exp (r i) - p • aeval (r i) g)‖ :=
        norm_sum_le _ _
      _ = ∑ i, ‖(b i : ℂ)‖ * ‖n • Complex.exp (r i) - p • aeval (r i) g‖ := by
        simp only [norm_mul]
      _ ≤ ∑ i, ‖(b i : ℂ)‖ * (c ^ p / (p - 1)!) := by
        exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hg (hr i)) (norm_nonneg _))
      _ = B * c ^ p / (p - 1)! := by rw [← Finset.sum_mul, mul_div_assoc]
  exact (not_lt_of_ge (one_le_norm_intCast hnonzero)) (hbound.trans_lt (hN p hpN))

/-- A finite collection of nonzero algebraic complex numbers has a common
integer polynomial with nonzero constant coefficient. -/
theorem exists_integer_polynomial_roots {ι : Type*} [Fintype ι]
    (r : ι → ℂ) (hr : ∀ i, IsAlgebraic ℤ (r i)) (h0 : ∀ i, r i ≠ 0) :
    ∃ f : ℤ[X], f.eval 0 ≠ 0 ∧ ∀ i, r i ∈ f.aroots ℂ := by
  classical
  choose q hq0 hqr using fun i =>
    (hr i).exists_nonzero_coeff_and_aeval_eq_zero
      (mem_nonZeroDivisors_iff_ne_zero.mpr (h0 i))
  refine ⟨∏ i, q i, ?_, ?_⟩
  · simp only [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simpa only [coeff_zero_eq_eval_zero] using hq0 i)
  · intro i
    apply mem_aroots.mpr
    constructor
    · exact Finset.prod_ne_zero_iff.mpr (fun j _ h => hq0 j (by rw [h]; simp))
    · rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hqr i)

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Evaluation of a formal exponential polynomial along a complex embedding. -/
def expEval (e : K →+* ℂ) : ExpPoly K →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ K
    { toFun := fun x => Complex.exp (e x.toAdd)
      map_one' := by simp
      map_mul' := by intro x y; simp [Complex.exp_add] }

@[simp] theorem expEval_apply (e : K →+* ℂ) (u : ExpPoly K) :
    expEval e u = ∑ x ∈ u.coeff.support, (u.coeff x : ℂ) * Complex.exp (e x) := rfl

@[simp] theorem expEval_single (e : K →+* ℂ) (x : K) (z : ℤ) :
    expEval e (AddMonoidAlgebra.single x z) = (z : ℂ) * Complex.exp (e x) := by
  simp [expEval, zsmul_eq_mul]

theorem expEval_galoisProduct_eq_zero [Fintype (K ≃ₐ[ℚ] K)]
    (e : K →+* ℂ) {u : ExpPoly K} (hu : expEval e u = 0) :
    expEval e (galoisProduct u) = 0 := by
  classical
  rw [galoisProduct, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (1 : K ≃ₐ[ℚ] K)) (by simpa using hu)

/-- Evaluate an integer polynomial and then apply a ring homomorphism. -/
theorem map_aeval_int (e : K →+* ℂ) (x : K) (g : ℤ[X]) :
    e (aeval x g) = aeval (e x) g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | monomial n z => simp [aeval_monomial]

/-- The integer polynomial moment theorem, transported to complex numbers. -/
theorem complex_moment_eq_intCast [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (e : K →+* ℂ) {u : ExpPoly K} (hu : IntegralSupport u)
    (hinv : ∀ σ : K ≃ₐ[ℚ] K, conjugate σ u = u) (g : ℤ[X]) :
    ∃ z : ℤ, (z : ℂ) = ∑ x ∈ u.coeff.support, (u.coeff x : ℂ) * aeval (e x) g := by
  obtain ⟨z, hz⟩ := moment_eq_intCast hu hinv g
  refine ⟨z, ?_⟩
  have h := congrArg e hz
  simpa only [map_intCast, moment, Finsupp.sum, map_sum, map_mul, map_aeval_int] using h

/-- An invariant integral-supported formal exponential polynomial with nonzero
constant coefficient cannot vanish under complex exponential evaluation. -/
theorem expEval_ne_zero_of_invariant_integral
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (e : K →+* ℂ) {u : ExpPoly K} (hu : IntegralSupport u)
    (hinv : ∀ σ : K ≃ₐ[ℚ] K, conjugate σ u = u) (h0 : u.coeff 0 ≠ 0) :
    expEval e u ≠ 0 := by
  classical
  let s := u.coeff.support.erase 0
  have hmem0 : 0 ∈ u.coeff.support := Finsupp.mem_support_iff.mpr h0
  have hs (x : s) : (x : K) ∈ u.coeff.support := Finset.mem_of_mem_erase x.property
  have hx0 (x : s) : (x : K) ≠ 0 := (Finset.mem_erase.mp x.property).1
  obtain ⟨f, hf, hfr⟩ := exists_integer_polynomial_roots (fun x : s => e x)
    (fun x => (map_isIntegral_int e (hu x (hs x))).isAlgebraic)
    (fun x => by simpa using e.injective.ne (hx0 x))
  have hm : ∀ g : ℤ[X], ∃ z : ℤ,
      (z : ℂ) = ∑ x : s, (u.coeff x : ℂ) * aeval (e x) g := by
    intro g
    obtain ⟨z, hz⟩ := complex_moment_eq_intCast e hu hinv g
    refine ⟨z - u.coeff 0 * g.eval 0, ?_⟩
    have hsplit := Finset.sum_erase_add u.coeff.support
      (fun x => (u.coeff x : ℂ) * aeval (e x) g) hmem0
    have heval0 : aeval (0 : ℂ) g = ((g.eval 0 : ℤ) : ℂ) := by
      rw [← coeff_zero_eq_aeval_zero', coeff_zero_eq_eval_zero]
      rfl
    rw [e.map_zero, heval0] at hsplit
    rw [Finset.sum_coe_sort s (fun x => (u.coeff x : ℂ) * aeval (e x) g)]
    push_cast
    dsimp [s]
    rw [← hz] at hsplit
    linear_combination -hsplit
  have hn := exp_sum_ne_zero_of_integer_moments (fun x : s => e x)
    (fun x : s => u.coeff x) f hf hfr hm (u.coeff 0) h0
  intro heval
  apply hn
  rw [Finset.sum_coe_sort s (fun x => (u.coeff x : ℂ) * Complex.exp (e x))]
  have hsplit := Finset.sum_erase_add u.coeff.support
    (fun x => (u.coeff x : ℂ) * Complex.exp (e x)) hmem0
  simp only [map_zero, Complex.exp_zero, mul_one] at hsplit
  change (u.coeff 0 : ℂ) + ∑ x ∈ s, (u.coeff x : ℂ) * Complex.exp (e x) = 0
  rw [add_comm, hsplit]
  exact heval

/-- Lindemann--Weierstrass for integer-coefficient exponential polynomials whose
exponents are algebraic integers in a finite Galois extension of the rationals.
The proof constructs its Galois symmetrization and its nonzero constant term. -/
theorem expEval_ne_zero_of_integralSupport
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (e : K →+* ℂ) {u : ExpPoly K} (hu : IntegralSupport u) (hu0 : u ≠ 0) :
    expEval e u ≠ 0 := by
  classical
  letI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  let v := galoisProduct u
  have hv : IntegralSupport v := hu.galoisProduct
  have hv0 : v ≠ 0 := galoisProduct_ne_zero hu0
  have hw0 : (v * reverseExponents v).coeff 0 ≠ 0 :=
    ne_of_gt (mul_reverseExponents_coeff_zero_pos hv0)
  have hwInv : ∀ σ : K ≃ₐ[ℚ] K,
      conjugate σ (v * reverseExponents v) = v * reverseExponents v := by
    intro σ
    simp only [map_mul, conjugate_reverseExponents]
    simp [v]
  have hnonzero := expEval_ne_zero_of_invariant_integral e
    (hv.mul hv.reverseExponents) hwInv hw0
  intro hzero
  apply hnonzero
  rw [map_mul, expEval_galoisProduct_eq_zero e hzero, zero_mul]

/-- An integer relation between exponentials of distinct algebraic integers in
a finite Galois extension is trivial. -/
theorem integer_exp_relation_of_integral
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {ι : Type*} [Fintype ι] (e : K →+* ℂ) (r : ι → K)
    (hr : Function.Injective r) (hint : ∀ i, IsIntegral ℤ (r i))
    (b : ι → ℤ) (hrel : ∑ i, (b i : ℂ) * Complex.exp (e (r i)) = 0) :
    ∀ i, b i = 0 := by
  classical
  let u : ExpPoly K := ∑ i, AddMonoidAlgebra.single (r i) (b i)
  have hcoeff (i : ι) : u.coeff (r i) = b i := by
    simp [u, hr.eq_iff, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hu : IntegralSupport u :=
    IntegralSupport.sum _ _ (fun i _ => IntegralSupport.single (hint i) (b i))
  have heval : expEval e u = 0 := by
    simpa only [u, map_sum, expEval_single] using hrel
  have hu0 : u = 0 := by
    by_contra h
    exact expEval_ne_zero_of_integralSupport e hu h heval
  intro i
  rw [← hcoeff, hu0]
  simp

end MatchgateWidth.LindemannAlgebraicPart
