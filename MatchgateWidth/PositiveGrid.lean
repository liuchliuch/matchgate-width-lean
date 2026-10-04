import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Basic.Complex.Basic

/-!
# Density of the positive-integer grid

This file formalizes Lemma 6.3 of arXiv:2610.00079v1. We use the algebraic
characterization of Zariski density: every polynomial vanishing on the set is
zero. We also state the result directly as equality of the polynomial-defined
Zariski closure with the whole affine space, and prove the finite simultaneous
polynomial-avoidance step used in Proposition 6.4.

The generic statements work over every characteristic-zero integral domain,
with any type of variables. In particular, they include the paper's finite
positive-integer grid in complex affine space (and even the case N = 0).
-/

namespace MatchgateWidth

open MvPolynomial

/-- The positive integers, embedded in a ring. -/
def positiveNaturals (R : Type*) [NatCast R] : Set R :=
  Set.range (fun n : ℕ => ((n + 1 : ℕ) : R))

/-- The positive-integer grid in affine space with coordinate type `σ`. -/
def positiveGrid (σ R : Type*) [NatCast R] : Set (σ → R) :=
  Set.pi Set.univ (fun _ => positiveNaturals R)

/-- Algebraic Zariski closure: the common zero set of all polynomials
vanishing on a given set. This avoids choosing a topology on the ambient
function type, which for `ℂ` also carries the usual analytic topology. -/
def polynomialZariskiClosure {σ R : Type*} [CommSemiring R]
    (S : Set (σ → R)) : Set (σ → R) :=
  {x | ∀ p : MvPolynomial σ R,
    (∀ y ∈ S, eval y p = 0) → eval x p = 0}

/-- The common zero set in `S`-valued affine space of polynomials with
coefficients in `R`, evaluated through the specified coefficient homomorphism. -/
def polynomialZeroLocus {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : Set (MvPolynomial σ R)) : Set (σ → S) :=
  {x | ∀ p ∈ P, eval₂ f x p = 0}

/-- A proper polynomial-defined zero set has a nonzero polynomial among its
defining equations. This extracts the certificate from properness; the
certificate is not an additional hypothesis. -/
theorem exists_nonzero_polynomial_of_proper_zeroLocus
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : Set (MvPolynomial σ R))
    (hproper : polynomialZeroLocus f P ≠ Set.univ) :
    ∃ p ∈ P, p ≠ 0 := by
  classical
  by_contra h
  apply hproper
  apply Set.eq_univ_of_forall
  intro x p hp
  have hz : p = 0 := by
    by_contra hne
    exact h ⟨p, hp, hne⟩
  rw [hz, eval₂_zero]

section IntegralDomain

variable {σ R : Type*} [CommRing R] [IsDomain R] [CharZero R]

omit [IsDomain R] in
/-- A positive-integer coordinate set is infinite in characteristic zero. -/
theorem positiveNaturals_infinite : (positiveNaturals R).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  exact Nat.succ_injective (Nat.cast_injective h)

/-- Polynomial-vanishing formulation of positive-grid Zariski density. -/
theorem eq_zero_of_eval_positiveGrid_eq_zero {p : MvPolynomial σ R}
    (h : ∀ x ∈ positiveGrid σ R, eval x p = 0) : p = 0 := by
  apply MvPolynomial.funext_set (fun _ => positiveNaturals R)
    (fun _ => positiveNaturals_infinite)
  intro x hx
  simpa only [map_zero] using h x hx

/-- The positive-integer grid has the whole affine space as its Zariski closure. -/
theorem positiveGrid_polynomialZariskiClosure :
    polynomialZariskiClosure (positiveGrid σ R) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x p hp
  rw [eq_zero_of_eval_positiveGrid_eq_zero hp, map_zero]

/-- Density with an explicit positive natural-number value in each coordinate. -/
theorem eq_zero_of_eval_positive_nat_eq_zero {p : MvPolynomial σ R}
    (h : ∀ a : σ → ℕ, (∀ i, 0 < a i) → eval (fun i => (a i : R)) p = 0) :
    p = 0 := by
  classical
  apply eq_zero_of_eval_positiveGrid_eq_zero
  intro x hx
  have hcoord : ∀ i, ∃ n : ℕ, ((n + 1 : ℕ) : R) = x i :=
    fun i => hx i (Set.mem_univ i)
  choose a ha using hcoord
  have heq : (fun i => ((a i + 1 : ℕ) : R)) = x := funext ha
  rw [← heq]
  exact h (fun i => a i + 1) (fun i => Nat.zero_lt_succ (a i))

/-- Every nonzero polynomial is nonzero at some positive-integer point. -/
theorem exists_positive_nat_eval_ne_zero (p : MvPolynomial σ R) (hp : p ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧ eval (fun i => (a i : R)) p ≠ 0 := by
  classical
  by_contra h
  apply hp
  apply eq_zero_of_eval_positive_nat_eq_zero
  intro a ha
  by_contra hne
  exact h ⟨a, ha, hne⟩

/-- A finite collection of nonzero polynomials can all be avoided at a single
positive-integer point. This is the product-avoidance step in Proposition 6.4. -/
theorem exists_positive_nat_forall_eval_ne_zero {ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial σ R) (hp : ∀ j ∈ s, p j ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      ∀ j ∈ s, eval (fun i => (a i : R)) (p j) ≠ 0 := by
  classical
  have hprod : (∏ j ∈ s, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨a, ha, h⟩ := exists_positive_nat_eval_ne_zero (∏ j ∈ s, p j) hprod
  refine ⟨a, ha, ?_⟩
  rw [map_prod] at h
  exact Finset.prod_ne_zero_iff.mp h

/-- Fintype-indexed form, convenient for all flattening minors or all bad widths. -/
theorem exists_positive_nat_forall_eval_ne_zero_fintype {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ R) (hp : ∀ j, p j ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      ∀ j, eval (fun i => (a i : R)) (p j) ≠ 0 := by
  simpa only [Finset.mem_univ, forall_const] using
    exists_positive_nat_forall_eval_ne_zero Finset.univ p (fun j _ => hp j)

/-- Simultaneous avoidance survives an injective change of coefficient ring.
This explicitly justifies treating rational defining polynomials as polynomials
evaluated at complex points. -/
theorem exists_positive_nat_forall_eval₂_ne_zero {S ι : Type*} [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f)
    (s : Finset ι) (p : ι → MvPolynomial σ R) (hp : ∀ j ∈ s, p j ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      ∀ j ∈ s, eval₂ f (fun i => (a i : S)) (p j) ≠ 0 := by
  obtain ⟨a, ha, h⟩ := exists_positive_nat_forall_eval_ne_zero s p hp
  refine ⟨a, ha, ?_⟩
  intro j hj
  have hmap : f (eval (fun i => (a i : R)) (p j)) =
      eval₂ f (fun i => (a i : S)) (p j) := by
    simpa only [eval₂_id, RingHom.comp_id, Function.comp_def, map_natCast] using
      eval₂_comp_left f (RingHom.id R) (fun i => (a i : R)) (p j)
  rw [← hmap]
  intro hz
  exact h j hj (hf (hz.trans (map_zero f).symm))

/-- The polynomial layer of Proposition 6.4: finitely many proper
polynomial-defined zero sets, and finitely many nonzero minor polynomials, can
be avoided simultaneously by a positive-integer table. The coefficients may
be embedded into another ring, so the statement includes rational defining
equations for complex algebraic sets.

This result does not assume or establish any matchgate-specific image bound.
Such a bound must separately provide the proper zero sets used as input. -/
theorem exists_positive_nat_avoiding_zeroLoci_and_minors
    {S ι κ : Type*} [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f)
    (s : Finset ι) (P : ι → Set (MvPolynomial σ R))
    (hproper : ∀ j ∈ s, polynomialZeroLocus f (P j) ≠ Set.univ)
    (t : Finset κ) (minor : κ → MvPolynomial σ R)
    (hminor : ∀ k ∈ t, minor k ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      (∀ j ∈ s, (fun i => (a i : S)) ∉ polynomialZeroLocus f (P j)) ∧
      ∀ k ∈ t, eval₂ f (fun i => (a i : S)) (minor k) ≠ 0 := by
  classical
  choose q hqmem hqne using fun j : {j // j ∈ s} =>
    exists_nonzero_polynomial_of_proper_zeroLocus f (P j) (hproper j j.property)
  let Q : ({j // j ∈ s} ⊕ {k // k ∈ t}) → MvPolynomial σ R :=
    Sum.elim q (fun k => minor k)
  have hQ : ∀ u, Q u ≠ 0 := by
    intro u
    cases u with
    | inl j => exact hqne j
    | inr k => exact hminor k k.property
  obtain ⟨a, ha, h⟩ := exists_positive_nat_forall_eval₂_ne_zero f hf
    Finset.univ Q (fun u _ => hQ u)
  refine ⟨a, ha, ?_, ?_⟩
  · intro j hj hmem
    exact h (.inl ⟨j, hj⟩) (Finset.mem_univ _)
      (hmem (q ⟨j, hj⟩) (hqmem ⟨j, hj⟩))
  · intro k hk
    exact h (.inr ⟨k, hk⟩) (Finset.mem_univ _)

end IntegralDomain

/-- Lemma 6.3, with precisely the paper's ambient complex affine N-space.
The claim also holds without the paper's unnecessary assumption `1 ≤ N`. -/
theorem lemma_6_3_positive_integer_grid_zariski_dense (N : ℕ) :
    polynomialZariskiClosure (positiveGrid (Fin N) ℂ) = Set.univ :=
  positiveGrid_polynomialZariskiClosure

/-- The complex-polynomial simultaneous avoidance needed in Proposition 6.4.
Rational-coefficient polynomials are also covered by the generic theorem above. -/
theorem positive_integer_table_avoids_finite_polynomials {σ ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial σ ℂ) (hp : ∀ j ∈ s, p j ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      ∀ j ∈ s, eval (fun i => (a i : ℂ)) (p j) ≠ 0 :=
  exists_positive_nat_forall_eval_ne_zero s p hp

/-- Proposition 6.4 uses nonzero rational defining polynomials but permits
arbitrary complex representations. Their positive-integer avoidance is valid
after extending evaluation to ℂ. -/
theorem positive_integer_table_avoids_rational_polynomials {σ ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial σ ℚ) (hp : ∀ j ∈ s, p j ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      ∀ j ∈ s, eval₂ (Rat.castHom ℂ) (fun i => (a i : ℂ)) (p j) ≠ 0 :=
  exists_positive_nat_forall_eval₂_ne_zero (Rat.castHom ℂ)
    (Rat.castHom ℂ).injective s p hp

/-- The exact coefficient fields of Proposition 6.4's polynomial-avoidance
step: proper rational-defined loci in complex affine space, together with
nonzero rational minor polynomials. -/
theorem positive_integer_table_avoids_rational_zeroLoci_and_minors
    {σ ι κ : Type*}
    (s : Finset ι) (P : ι → Set (MvPolynomial σ ℚ))
    (hproper : ∀ j ∈ s,
      polynomialZeroLocus (Rat.castHom ℂ) (P j) ≠ Set.univ)
    (t : Finset κ) (minor : κ → MvPolynomial σ ℚ)
    (hminor : ∀ k ∈ t, minor k ≠ 0) :
    ∃ a : σ → ℕ, (∀ i, 0 < a i) ∧
      (∀ j ∈ s, (fun i => (a i : ℂ)) ∉
        polynomialZeroLocus (Rat.castHom ℂ) (P j)) ∧
      ∀ k ∈ t, eval₂ (Rat.castHom ℂ) (fun i => (a i : ℂ)) (minor k) ≠ 0 :=
  exists_positive_nat_avoiding_zeroLoci_and_minors (Rat.castHom ℂ)
    (Rat.castHom ℂ).injective s P hproper t minor hminor

end MatchgateWidth
