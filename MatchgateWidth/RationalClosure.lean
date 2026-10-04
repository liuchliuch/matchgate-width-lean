import MatchgateWidth.PolynomialImage
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Rational definition of polynomial image closures

The descent argument extracts rational coefficient polynomials using linear
coordinate functionals on a rational basis of the complex numbers.
-/

namespace MatchgateWidth

open MvPolynomial

noncomputable section

/-- Apply a rational-linear functional separately to each coefficient. -/
def rationalCoefficientProjection {τ : Type*} (f : ℂ →ₗ[ℚ] ℚ)
    (q : MvPolynomial τ ℂ) : MvPolynomial τ ℚ :=
  AddMonoidAlgebra.map f.toAddMonoidHom q

@[simp] theorem coeff_rationalCoefficientProjection {τ : Type*}
    (f : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial τ ℂ) (m : τ →₀ ℕ) :
    (rationalCoefficientProjection f q).coeff m = f (q.coeff m) := rfl

/-- Rational evaluation commutes with rational-linear coefficient extraction. -/
theorem eval_rationalCoefficientProjection {τ : Type*}
    (f : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial τ ℂ) (x : τ → ℚ) :
    eval x (rationalCoefficientProjection f q) =
      f (eval (fun i => (x i : ℂ)) q) := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c =>
    simp only [rationalCoefficientProjection, monomial, AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.map_single]
    change eval x (MvPolynomial.monomial m (f c)) =
      f (eval (fun i => (x i : ℂ)) (MvPolynomial.monomial m c))
    simp only [eval_monomial]
    have he : (m.prod fun i n => (x i : ℂ) ^ n) =
        ((m.prod fun i n => x i ^ n : ℚ) : ℂ) := by
      simp only [Finsupp.prod, Rat.cast_prod, Rat.cast_pow]
    rw [he, mul_comm c, ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]
  | add p q hp hq =>
    simp only [rationalCoefficientProjection, AddMonoidAlgebra.map_add,
      map_add, ← hp, ← hq]

/-- Every complex polynomial is a finite complex-linear combination of its
rational coefficient projections. -/
theorem exists_rational_projection_decomposition {τ : Type*}
    (q : MvPolynomial τ ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (f : ι → ℂ →ₗ[ℚ] ℚ),
      q = ∑ i, a i • map (Rat.castHom ℂ) (rationalCoefficientProjection (f i) q) := by
  classical
  let b := Module.Free.chooseBasis ℚ ℂ
  let t := q.support.biUnion (fun m => (b.repr (q.coeff m)).support)
  let f (i : t) : ℂ →ₗ[ℚ] ℚ := b.coord i
  refine ⟨t, inferInstance, fun i => b i, f, ?_⟩
  apply MvPolynomial.ext
  intro m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_rationalCoefficientProjection]
  by_cases hm : m ∈ q.support
  · have hsubset : (b.repr (q.coeff m)).support ⊆ t := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨m, hm, hi⟩
    have hb := b.linearCombination_repr (q.coeff m)
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hb
    calc
      q.coeff m = ∑ i ∈ (b.repr (q.coeff m)).support,
          b.repr (q.coeff m) i • b i := hb.symm
      _ = ∑ i ∈ t, b.repr (q.coeff m) i • b i := by
        exact Finset.sum_subset hsubset (by
          intro i hit hin
          simp only [Finsupp.notMem_support_iff.mp hin, zero_smul])
      _ = ∑ i : t, b i • (Rat.castHom ℂ) (f i (q.coeff m)) := by
        simp only [f, Module.Basis.coord_apply]
        rw [← Finset.sum_coe_sort t (fun i => b.repr (q.coeff m) i • b i)]
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.smul_def, mul_comm]
  · have hz : q.coeff m = 0 := notMem_support_iff.mp hm
    simp [hz, f]

/-- The closure of any set of rational points is exactly the complex zero
locus of its rational vanishing polynomials. -/
theorem polynomialZariskiClosure_rational_points {τ : Type*}
    (S : Set (τ → ℚ)) :
    polynomialZariskiClosure ((fun x i => (x i : ℂ)) '' S) =
      polynomialZeroLocus (Rat.castHom ℂ)
        {p : MvPolynomial τ ℚ | ∀ x ∈ S, eval x p = 0} := by
  classical
  ext x
  constructor
  · intro hx p hp
    have hv := hx (map (Rat.castHom ℂ) p) (by
      rintro y ⟨a, ha, rfl⟩
      rw [eval_map]
      change eval₂ (Rat.castHom ℂ) ((Rat.castHom ℂ) ∘ a) p = 0
      rw [← eval₂_comp, hp a ha, map_zero])
    simpa only [eval_map] using hv
  · intro hx q hq
    obtain ⟨ι, inst, a, f, hdecomp⟩ := exists_rational_projection_decomposition q
    let := inst
    have hf (i : ι) : ∀ y ∈ S, eval y (rationalCoefficientProjection (f i) q) = 0 := by
      intro y hy
      rw [eval_rationalCoefficientProjection, hq _ ⟨y, hy, rfl⟩, map_zero]
    rw [hdecomp, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [smul_eval, eval_map, hx _ (hf i), mul_zero]

/-- Complex points in an arbitrary union of rational polynomial charts. -/
def rationalPolynomialChartUnion {τ ι : Type*} {σ : ι → Type*}
    (p : ∀ i, τ → MvPolynomial (σ i) ℚ) : Set (τ → ℂ) :=
  {y | ∃ i x, polynomialMap (Rat.castHom ℂ) (p i) x = y}

private theorem rationalChartPoint_map {σ τ : Type*}
    (p : τ → MvPolynomial σ ℚ) (a : σ → ℚ) :
    (fun t => ((polynomialMap (RingHom.id ℚ) p a t : ℚ) : ℂ)) =
      polynomialMap (Rat.castHom ℂ) p (fun t => (a t : ℂ)) := by
  funext t
  exact MvPolynomial.eval₂_comp (Rat.castHom ℂ) a (p t)

private theorem eval_complex_chart_substitution {σ τ : Type*}
    (p : τ → MvPolynomial σ ℚ) (q : MvPolynomial τ ℂ) (x : σ → ℂ) :
    eval x (aeval (fun t => map (Rat.castHom ℂ) (p t)) q) =
      eval (polynomialMap (Rat.castHom ℂ) p x) q := by
  rw [aeval_eq_bind₁]
  change aeval x (bind₁ (fun t => map (Rat.castHom ℂ) (p t)) q) = _
  rw [aeval_bind₁]
  change eval (fun t => eval x (map (Rat.castHom ℂ) (p t))) q = _
  apply congrArg (fun y => eval y q)
  funext t
  exact eval_map (Rat.castHom ℂ) x (p t)

/-- Rational parameter values are Zariski dense in every rational polynomial
chart, also simultaneously for an arbitrary family of charts. -/
theorem rationalPolynomialChartUnion_closure_eq_rational_points
    {τ ι : Type*} {σ : ι → Type*}
    (p : ∀ i, τ → MvPolynomial (σ i) ℚ) :
    polynomialZariskiClosure (rationalPolynomialChartUnion p) =
      polynomialZariskiClosure ((fun y t => (y t : ℂ)) ''
        {y : τ → ℚ | ∃ i a, polynomialMap (RingHom.id ℚ) (p i) a = y}) := by
  ext x
  have hvan (q : MvPolynomial τ ℂ) :
      (∀ y ∈ rationalPolynomialChartUnion p, eval y q = 0) ↔
      (∀ y ∈ ((fun y t => (y t : ℂ)) ''
        {y : τ → ℚ | ∃ i a, polynomialMap (RingHom.id ℚ) (p i) a = y}),
          eval y q = 0) := by
    constructor
    · intro h y hy
      obtain ⟨_, ⟨i, a, rfl⟩, rfl⟩ := hy
      dsimp only
      rw [rationalChartPoint_map]
      exact h _ ⟨i, (fun t => (a t : ℂ)), rfl⟩
    · intro h y hy
      obtain ⟨i, a, rfl⟩ := hy
      have hz : aeval (fun t => map (Rat.castHom ℂ) (p i t)) q = 0 := by
        apply eq_zero_of_eval_positive_nat_eq_zero
        intro n hn
        rw [eval_complex_chart_substitution]
        have hv := h _ ⟨polynomialMap (RingHom.id ℚ) (p i) (fun t => (n t : ℚ)),
          ⟨i, (fun t => (n t : ℚ)), rfl⟩, rfl⟩
        dsimp only at hv
        rw [rationalChartPoint_map] at hv
        simpa only [Rat.cast_natCast] using hv
      have hv := congrArg (eval a) hz
      simpa only [eval_complex_chart_substitution, map_zero] using hv
  simp only [polynomialZariskiClosure, Set.mem_ofPred_eq]
  simp only [hvan]

/-- An exact rational system of equations defining the complex image closure.
This is rational definition of the closure itself, rather than merely a
rational hypersurface containing it. -/
theorem rationalPolynomialChartUnion_closure_defined_over_rat
    {τ ι : Type*} {σ : ι → Type*}
    (p : ∀ i, τ → MvPolynomial (σ i) ℚ) :
    ∃ P : Set (MvPolynomial τ ℚ),
      polynomialZariskiClosure (rationalPolynomialChartUnion p) =
        polynomialZeroLocus (Rat.castHom ℂ) P := by
  rw [rationalPolynomialChartUnion_closure_eq_rational_points]
  exact ⟨_, polynomialZariskiClosure_rational_points _⟩

end
end MatchgateWidth
