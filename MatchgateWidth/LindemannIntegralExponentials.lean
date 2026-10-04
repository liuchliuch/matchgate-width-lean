import MatchgateWidth.LindemannAlgebraicPart
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Localization.Integer

/-!
# Rational linear independence of exponentials of algebraic integers

The finite Galois extension required by the algebraic argument is constructed
inside the complex numbers by adjoining all roots of the product of the minimal
polynomials. The result is sufficient for the prime-square-root exponential
construction: its expanded monomial exponents are algebraic integers.
-/

noncomputable section
namespace MatchgateWidth.LindemannAlgebraicPart
open scoped BigOperators
open Polynomial

/-- Any finite set of algebraic complex numbers lies in a finite Galois
intermediate field over the rationals. -/
theorem exists_finite_galois_field {ι : Type*} [Fintype ι]
    (r : ι → ℂ) (hr : ∀ i, IsIntegral ℚ (r i)) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
      ∀ i, r i ∈ K := by
  classical
  let f : ℚ[X] := ∏ i, minpoly ℚ (r i)
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => minpoly.ne_zero (hr i))
  let K := IntermediateField.adjoin ℚ (f.rootSet ℂ)
  letI : f.IsSplittingField ℚ K :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  letI : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K f
  letI : Normal ℚ K := Normal.of_isSplittingField f
  letI : IsGalois ℚ K := {}
  refine ⟨K, inferInstance, inferInstance, ?_⟩
  intro i
  apply IntermediateField.subset_adjoin ℚ (f.rootSet ℂ)
  apply Polynomial.mem_rootSet.mpr
  refine ⟨hf, ?_⟩
  rw [show f = ∏ j, minpoly ℚ (r j) from rfl, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval ℚ (r i))

/-- Every integer linear relation between exponentials of distinct algebraic
integers is trivial. No transcendence assertion is assumed. -/
theorem integer_exp_relation {ι : Type*} [Fintype ι]
    (r : ι → ℂ) (hr : Function.Injective r) (hint : ∀ i, IsIntegral ℤ (r i))
    (b : ι → ℤ) (hrel : ∑ i, (b i : ℂ) * Complex.exp (r i) = 0) :
    ∀ i, b i = 0 := by
  obtain ⟨K, hfin, hgal, hK⟩ := exists_finite_galois_field r (fun i => (hint i).tower_top)
  letI : FiniteDimensional ℚ K := hfin
  letI : IsGalois ℚ K := hgal
  let rK : ι → K := fun i => ⟨r i, hK i⟩
  have hinjK : Function.Injective rK := by
    intro i j h
    apply hr
    exact congrArg Subtype.val h
  have hintK : ∀ i, IsIntegral ℤ (rK i) := by
    intro i
    exact isIntegral_algebraMap_iff.mp (hint i)
  exact integer_exp_relation_of_integral K.val.toRingHom rK hinjK hintK b hrel

/-- Every rational linear relation between exponentials of distinct algebraic
integers is trivial, by clearing the coefficient denominators. -/
theorem rational_exp_relation {ι : Type*} [Fintype ι]
    (r : ι → ℂ) (hr : Function.Injective r) (hint : ∀ i, IsIntegral ℤ (r i))
    (b : ι → ℚ) (hrel : ∑ i, (b i : ℂ) * Complex.exp (r i) = 0) :
    ∀ i, b i = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) b
  choose a ha using hd
  have hcast (i : ι) : (a i : ℂ) = (d.val : ℂ) * (b i : ℂ) := by
    have hai : (a i : ℚ) = (d.val : ℚ) * b i := by
      simpa only [eq_intCast, zsmul_eq_mul, Int.cast_eq] using ha i
    exact_mod_cast hai
  have ha0 : ∀ i, a i = 0 := integer_exp_relation r hr hint a (by
    simp_rw [hcast, mul_assoc]
    rw [← Finset.mul_sum, hrel, mul_zero])
  have hd0 : (d.val : ℚ) ≠ 0 := by
    exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  intro i
  have h := ha i
  rw [ha0 i] at h
  simpa only [eq_intCast, Int.cast_zero, zsmul_eq_mul, Int.cast_eq,
    eq_comm, mul_eq_zero, hd0, false_or] using h

/-- The rational linear independence form of Lindemann--Weierstrass for
algebraic-integer exponents. -/
theorem linearIndependent_exp_integral {ι : Type*}
    (r : ι → ℂ) (hr : Function.Injective r) (hint : ∀ i, IsIntegral ℤ (r i)) :
    LinearIndependent ℚ (fun i => Complex.exp (r i)) := by
  rw [linearIndependent_iff']
  intro s b hrel i hi
  have hsub : ∑ x : s, (b x : ℂ) * Complex.exp (r x) = 0 := by
    rw [Finset.sum_coe_sort s (fun x => (b x : ℂ) * Complex.exp (r x))]
    simpa only [Rat.smul_def] using hrel
  have hzero := rational_exp_relation (fun x : s => r x)
    (hr.comp Subtype.val_injective) (fun x => hint x) (fun x => b x) hsub
  exact hzero ⟨i, hi⟩

end MatchgateWidth.LindemannAlgebraicPart
