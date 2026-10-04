import MatchgateWidth.PositiveGrid
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Polynomial parameter-count obstruction

A polynomial map with fewer parameters than target coordinates satisfies a
nonzero polynomial relation. This file obtains the relation from mathlib's
transcendence-degree theorem for multivariate polynomial rings, rather than
assuming a dimension or non-density conclusion.

For rational coefficient maps evaluated on complex points, the relation cuts
out a proper rational-defined zero locus. Products of relations give the same
conclusion for finitely many charts, even with different parameter counts.
These are the chart-level algebraic ingredients for Sections 5.1–5.4 of
arXiv:2610.00079v1; no claim about covering matchgate signatures is assumed here.
-/

namespace MatchgateWidth

open MvPolynomial

/-- A polynomial map, evaluated using the chosen coefficient homomorphism. -/
def polynomialMap {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : τ → MvPolynomial σ R) (x : σ → S) : τ → S :=
  fun i => eval₂ f x (p i)

/-- The set of values of a polynomial map. -/
def polynomialImage {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : τ → MvPolynomial σ R) : Set (τ → S) :=
  Set.range (polynomialMap f p)

/-- Fewer parameters than coordinates force a nonzero polynomial relation.
This is an actual existence theorem for the relation, not a theorem conditional
on a supplied relation or on properness of the image closure. -/
theorem exists_nonzero_polynomial_relation
    {d N : ℕ} (h : d < N) (p : Fin N → MvPolynomial (Fin d) ℚ) :
    ∃ q : MvPolynomial (Fin N) ℚ, q ≠ 0 ∧ aeval p q = 0 := by
  classical
  by_contra! hno
  have hi : AlgebraicIndependent ℚ p := by
    rw [algebraicIndependent_iff]
    intro q hq
    by_contra hne
    exact hno q hne hq
  have hcard := hi.cardinalMk_le_trdeg
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
    Cardinal.lift_natCast] at hcard
  have hn : N ≤ d := by exact_mod_cast hcard
  exact (Nat.not_le_of_lt h) hn

/-- Substitution relations remain zero after evaluating the parameters in any
commutative semiring receiving the coefficient ring. -/
theorem eval₂_polynomialMap_eq_zero_of_relation
    {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : τ → MvPolynomial σ R)
    (q : MvPolynomial τ R) (hq : aeval p q = 0) (x : σ → S) :
    eval₂ f (polynomialMap f p x) q = 0 := by
  change eval₂ f (fun i => eval₂ f x (p i)) q = 0
  have h := congrArg (eval₂Hom f x) hq
  simpa only [aeval_eq_bind₁, eval₂Hom_bind₁, map_zero, coe_eval₂Hom, polynomialMap] using h

/-- The image is contained in the zero locus of any substitution relation. -/
theorem polynomialImage_subset_zeroLocus_of_relation
    {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : τ → MvPolynomial σ R)
    (q : MvPolynomial τ R) (hq : aeval p q = 0) :
    polynomialImage f p ⊆ polynomialZeroLocus f {q} := by
  rintro _ ⟨x, rfl⟩ r hr
  have hrq : r = q := Set.mem_singleton_iff.mp hr
  subst r
  exact eval₂_polynomialMap_eq_zero_of_relation f p q hq x

/-- A nonzero rational polynomial defines a proper zero locus in complex
space. Positive-integer points already witness its properness. -/
theorem rational_polynomial_zeroLocus_ne_univ {τ : Type*}
    (q : MvPolynomial τ ℚ) (hq : q ≠ 0) :
    polynomialZeroLocus (Rat.castHom ℂ) {q} ≠ Set.univ := by
  obtain ⟨a, _, ha⟩ := positive_integer_table_avoids_rational_polynomials
    ({()} : Finset Unit) (fun _ : Unit => q) (by simpa using hq)
  intro h
  have hmem : (fun i => (a i : ℂ)) ∈
      polynomialZeroLocus (Rat.castHom ℂ) {q} := by rw [h]; trivial
  exact ha () (Finset.mem_singleton_self ()) (hmem q (Set.mem_singleton q))

/-- Every rational polynomial map with fewer parameters than coordinates has
its complex image in a proper, rational-defined hypersurface. -/
theorem polynomialImage_subset_proper_rational_zeroLocus
    {d N : ℕ} (h : d < N) (p : Fin N → MvPolynomial (Fin d) ℚ) :
    ∃ q : MvPolynomial (Fin N) ℚ, q ≠ 0 ∧
      polynomialImage (Rat.castHom ℂ) p ⊆
        polynomialZeroLocus (Rat.castHom ℂ) {q} ∧
      polynomialZeroLocus (Rat.castHom ℂ) {q} ≠ Set.univ := by
  obtain ⟨q, hq, hrel⟩ := exists_nonzero_polynomial_relation h p
  exact ⟨q, hq, polynomialImage_subset_zeroLocus_of_relation _ p q hrel,
    rational_polynomial_zeroLocus_ne_univ q hq⟩

/-- The nonzero relation also witnesses failure of polynomial Zariski density
after extending the rational coefficients to complex coefficients. -/
theorem polynomialImage_polynomialZariskiClosure_ne_univ
    {d N : ℕ} (h : d < N) (p : Fin N → MvPolynomial (Fin d) ℚ) :
    polynomialZariskiClosure (polynomialImage (Rat.castHom ℂ) p) ≠ Set.univ := by
  obtain ⟨q, hq, hrel⟩ := exists_nonzero_polynomial_relation h p
  obtain ⟨a, _, ha⟩ := positive_integer_table_avoids_rational_polynomials
    ({()} : Finset Unit) (fun _ : Unit => q) (by simpa using hq)
  intro hall
  have hc : (fun i => (a i : ℂ)) ∈
      polynomialZariskiClosure (polynomialImage (Rat.castHom ℂ) p) := by
    rw [hall]; trivial
  have hv : eval (fun i => (a i : ℂ)) (map (Rat.castHom ℂ) q) = 0 := by
    apply hc
    rintro _ ⟨x, rfl⟩
    rw [eval_map]
    exact eval₂_polynomialMap_eq_zero_of_relation _ p q hrel x
  apply ha () (Finset.mem_singleton_self ())
  simpa only [eval_map] using hv

/-- A finite union of rational polynomial charts of strictly smaller parameter
count satisfies a single nonzero rational equation. The parameter count may
vary with the chart, and the theorem also includes an empty family of charts. -/
theorem finite_polynomialImages_subset_proper_rational_zeroLocus
    {ι : Type*} {N : ℕ} (s : Finset ι) (d : ι → ℕ)
    (p : ∀ j, Fin N → MvPolynomial (Fin (d j)) ℚ)
    (h : ∀ j ∈ s, d j < N) :
    ∃ q : MvPolynomial (Fin N) ℚ, q ≠ 0 ∧
      (∀ j ∈ s, polynomialImage (Rat.castHom ℂ) (p j) ⊆
        polynomialZeroLocus (Rat.castHom ℂ) {q}) ∧
      polynomialZeroLocus (Rat.castHom ℂ) {q} ≠ Set.univ := by
  classical
  choose q hq hrel using fun j : {j // j ∈ s} =>
    exists_nonzero_polynomial_relation (h j j.property) (p j)
  let Q : MvPolynomial (Fin N) ℚ := ∏ j, q j
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hq j)
  refine ⟨Q, hQ, ?_, rational_polynomial_zeroLocus_ne_univ Q hQ⟩
  intro j hj y hy r hr
  have hrQ : r = Q := Set.mem_singleton_iff.mp hr
  subst r
  obtain ⟨x, rfl⟩ := hy
  change eval₂Hom (Rat.castHom ℂ) (polynomialMap (Rat.castHom ℂ) (p j) x)
    (∏ k, q k) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (i := ⟨j, hj⟩) (Finset.mem_univ _)
  simpa only [coe_eval₂Hom] using
    eval₂_polynomialMap_eq_zero_of_relation (Rat.castHom ℂ) (p j) (q ⟨j, hj⟩)
      (hrel ⟨j, hj⟩) x

end MatchgateWidth
