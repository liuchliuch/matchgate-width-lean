import MatchgateWidth.PfaffianCharts
import MatchgateWidth.PolynomialImage
import MatchgateWidth.StarContraction
import MatchgateWidth.WidthBudget
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Positive-integer obstruction for sampled Pfaffian-chart stars

A sampled star uses two shared width-`r` signed pivot-Pfaffian charts, and one
arity-`k*r` central chart. This file constructs its actual coordinate polynomial
map, proves the exact parameter count `D k r`, and obtains a proper rational
zero locus whenever `D k r < 2^k`. Finite positive-grid avoidance gives a
positive-integer Boolean table with all one-versus-rest flattenings of rank two
which has no low-budget chart-star representation.

The family here is explicitly chart-defined. No graph-to-matchgate-identity,
matchgate-identity-to-chart, or planar realization theorem is asserted.
-/

namespace MatchgateWidth

noncomputable section

/-- Fixed discrete data of a signed pivot chart. -/
abbrev PfaffianChartChoice (s : ℕ) :=
  BooleanInput s × (BooleanInput s → Fin 2)

/-- The two sampler choices are shared by every port. -/
abbrev StarChartChoice (k r : ℕ) :=
  (Fin 2 → PfaffianChartChoice r) × PfaffianChartChoice (k * r)

/-- Two sampler parameter sets and a single central parameter set. -/
abbrev StarChartParameter (k r : ℕ) :=
  (Fin 2 × PfaffianChartParameter r) ⊕ PfaffianChartParameter (k * r)

@[simp] theorem card_starChartParameter (k r : ℕ) :
    Fintype.card (StarChartParameter k r) = D k r := by
  simp [StarChartParameter, D, delta, Nat.add_comm]

@[simp] theorem card_booleanInput (k : ℕ) :
    Fintype.card (BooleanInput k) = 2 ^ k := by
  simp [BooleanInput]

/-- Flatten independent ordered `r`-bit words into the central `k*r` ports.
`finProdFinEquiv` places block `i` at positions `i*r` through `i*r+r-1`. -/
def flattenBooleanBlocks {k r : ℕ} (x : Fin k → BooleanInput r) :
    BooleanInput (k * r) :=
  fun j => x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

@[simp] theorem flattenBooleanBlocks_apply {k r : ℕ}
    (x : Fin k → BooleanInput r) (i : Fin k) (j : Fin r) :
    flattenBooleanBlocks x (finProdFinEquiv (i, j)) = x i j := by
  simp [flattenBooleanBlocks]

/-- The block flattening is a genuine equivalence, including zero block width. -/
def booleanBlocksEquiv (k r : ℕ) :
    (Fin k → BooleanInput r) ≃ BooleanInput (k * r) where
  toFun := flattenBooleanBlocks
  invFun := fun z i j => z (finProdFinEquiv (i, j))
  left_inv := by intro x; funext i j; simp
  right_inv := by
    intro z
    funext j
    exact congrArg z (finProdFinEquiv.apply_symm_apply j)

/-- The actual sampled star contraction over independent block words. -/
def sampledChartStar {k r : ℕ} {R : Type*} [CommRing R]
    (c : StarChartChoice k r) (a : StarChartParameter k r → R) :
    BooleanTable k R :=
  fun z => starContract
    (fun x => pfaffianPivotChart c.2.1 c.2.2 (fun t => a (.inr t))
      (flattenBooleanBlocks x))
    (fun i => pfaffianPivotChart (c.1 (z i)).1 (c.1 (z i)).2
      (fun t => a (.inl (z i, t))))

/-- Unfolding the contraction displays one independently summed block per port. -/
theorem sampledChartStar_eq_sum {k r : ℕ} {R : Type*} [CommRing R]
    (c : StarChartChoice k r) (a : StarChartParameter k r → R)
    (z : BooleanInput k) :
    sampledChartStar c a z =
      ∑ x : Fin k → BooleanInput r,
        pfaffianPivotChart c.2.1 c.2.2 (fun t => a (.inr t))
          (flattenBooleanBlocks x) *
        ∏ i, pfaffianPivotChart (c.1 (z i)).1 (c.1 (z i)).2
          (fun t => a (.inl (z i, t))) (x i) := by
  classical
  unfold sampledChartStar starContract
  apply Finset.sum_congr (by ext; simp)
  intro x _
  rfl

/-- Fixed signed pivot charts commute with coefficient homomorphisms. -/
theorem pfaffianPivotChart_map {s : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2)
    (a : PfaffianChartParameter s → R) (z : BooleanInput s) :
    f (pfaffianPivotChart pivot signs a z) =
      pfaffianPivotChart pivot signs (fun t => f (a t)) z := by
  simp only [pfaffianPivotChart, map_mul, map_pow, map_neg, map_one,
    pfaffianChart_map]

/-- The entire finite star contraction commutes with ring homomorphisms. -/
theorem sampledChartStar_map {k r : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (c : StarChartChoice k r) (a : StarChartParameter k r → R)
    (z : BooleanInput k) :
    f (sampledChartStar c a z) = sampledChartStar c (fun t => f (a t)) z := by
  classical
  simp only [sampledChartStar_eq_sum, map_sum, map_mul, map_prod,
    pfaffianPivotChart_map]

/-- Actual rational coordinate polynomials on exactly `D k r` variables. -/
def sampledChartStarPolynomial {k r : ℕ} (c : StarChartChoice k r)
    (z : BooleanInput k) : MvPolynomial (StarChartParameter k r) ℚ :=
  sampledChartStar c MvPolynomial.X z

/-- The coordinate polynomial map evaluates to the stated contraction. -/
theorem eval₂_sampledChartStarPolynomial {k r : ℕ} {R : Type*} [CommRing R]
    (f : ℚ →+* R) (c : StarChartChoice k r)
    (a : StarChartParameter k r → R) (z : BooleanInput k) :
    MvPolynomial.eval₂ f a (sampledChartStarPolynomial c z) =
      sampledChartStar c a z := by
  change (MvPolynomial.eval₂Hom f a) (sampledChartStarPolynomial c z) = _
  unfold sampledChartStarPolynomial
  rw [sampledChartStar_map]
  simp

/-- Exact identification of the chart-star family with the polynomial image. -/
theorem sampledChartStar_range_eq_polynomialImage {k r : ℕ}
    (c : StarChartChoice k r) :
    Set.range (sampledChartStar (R := ℂ) c) =
      polynomialImage (Rat.castHom ℂ) (sampledChartStarPolynomial c) := by
  congr 1
  funext a z
  exact (eval₂_sampledChartStarPolynomial (Rat.castHom ℂ) c a z).symm

/-- The parameter-count relation with arbitrary finite index types. -/
theorem exists_nonzero_polynomial_relation_fintype
    {σ τ : Type} [Fintype σ] [Fintype τ]
    (h : Fintype.card σ < Fintype.card τ) (p : τ → MvPolynomial σ ℚ) :
    ∃ q : MvPolynomial τ ℚ, q ≠ 0 ∧ MvPolynomial.aeval p q = 0 := by
  classical
  by_contra! hno
  have hi : AlgebraicIndependent ℚ p := by
    rw [algebraicIndependent_iff]
    intro q hq
    by_contra hne
    exact hno q hne hq
  have hcard := hi.cardinalMk_le_trdeg
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.lift_natCast] at hcard
  have hn : Fintype.card τ ≤ Fintype.card σ := by exact_mod_cast hcard
  exact (Nat.not_le_of_lt h) hn

/-- A chart-defined representation; it makes no assertion about graph signatures. -/
def HasChartStarRepresentation (k r : ℕ) (f : BooleanTable k ℂ) : Prop :=
  ∃ c : StarChartChoice k r, ∃ a : StarChartParameter k r → ℂ,
    sampledChartStar c a = f

/-- All discrete charts at a low-budget width satisfy a single nonzero rational
relation, so their union lies in a proper rational-defined hypersurface. -/
theorem chartStars_subset_proper_rational_zeroLocus {k r : ℕ}
    (h : D k r < 2 ^ k) :
    ∃ q : MvPolynomial (BooleanInput k) ℚ, q ≠ 0 ∧
      (∀ f, HasChartStarRepresentation k r f →
        f ∈ polynomialZeroLocus (Rat.castHom ℂ) {q}) ∧
      polynomialZeroLocus (Rat.castHom ℂ) {q} ≠ Set.univ := by
  classical
  have hc : Fintype.card (StarChartParameter k r) <
      Fintype.card (BooleanInput k) := by
    rw [card_starChartParameter, card_booleanInput]
    exact h
  choose q hq hrel using fun c : StarChartChoice k r =>
    exists_nonzero_polynomial_relation_fintype hc (sampledChartStarPolynomial c)
  let Q : MvPolynomial (BooleanInput k) ℚ := ∏ c, q c
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hq c)
  refine ⟨Q, hQ, ?_, rational_polynomial_zeroLocus_ne_univ Q hQ⟩
  rintro f ⟨c, a, rfl⟩ p hp
  have hpQ : p = Q := Set.mem_singleton_iff.mp hp
  subst p
  change MvPolynomial.eval₂Hom (Rat.castHom ℂ) (sampledChartStar c a) (∏ d, q d) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (i := c) (Finset.mem_univ _)
  have hv := eval₂_polynomialMap_eq_zero_of_relation (Rat.castHom ℂ)
    (sampledChartStarPolynomial c) (q c) (hrel c) a
  change MvPolynomial.eval₂ (Rat.castHom ℂ)
    (fun z => MvPolynomial.eval₂ (Rat.castHom ℂ) a (sampledChartStarPolynomial c z))
    (q c) = 0 at hv
  simp_rw [eval₂_sampledChartStarPolynomial] at hv
  exact hv

/-- A positive-integer full-flattening-rank obstruction to every low-budget
chart-star representation, simultaneously at all widths. -/
theorem exists_positive_integer_table_obstructing_lowBudget_chartStars
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ r, HasChartStarRepresentation k r (fun z => (a z : ℂ)) →
        2 ^ k ≤ D k r) ∧
      ∀ i : Fin k,
        (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2 := by
  classical
  let W := {r : ℕ // r ∈ lowBudgetFinset k}
  choose q hq hcover hproper using fun r : W =>
    chartStars_subset_proper_rational_zeroLocus (mem_lowBudgetFinset.mp r.property)
  obtain ⟨a, ha, havoid, hrank⟩ :=
    exists_positive_integer_table_avoiding_loci_all_flattenings_rank_two k hk
      (Finset.univ : Finset W) (fun r => {q r}) (fun r _ => hproper r)
  refine ⟨a, ha, ?_, hrank⟩
  intro r hrep
  by_contra hbudget
  have hr : r ∈ lowBudgetFinset k := mem_lowBudgetFinset.mpr (by omega)
  exact havoid ⟨r, hr⟩ (Finset.mem_univ _) (hcover ⟨r, hr⟩ _ hrep)

/-- Algebraic independence also excludes every low-budget chart-star image,
without any positive-integer specialization. -/
theorem algebraicIndependent_table_chartStar_budget {k r : ℕ}
    (f : BooleanTable k ℂ) (hf : AlgebraicIndependent ℚ f)
    (hrep : HasChartStarRepresentation k r f) :
    2 ^ k ≤ D k r := by
  by_contra hbudget
  obtain ⟨q, hq, hcover, _⟩ :=
    chartStars_subset_proper_rational_zeroLocus (k := k) (r := r) (by omega)
  apply hq
  apply hf.eq_zero_of_aeval_eq_zero
  have hz := hcover f hrep q (Set.mem_singleton q)
  rw [show Rat.castHom ℂ = algebraMap ℚ ℂ from Subsingleton.elim _ _] at hz
  simpa only [MvPolynomial.aeval_def] using hz

/-- The integer-ceiling width bound for a positive-integer full-rank table.
The conclusion refers solely to the explicitly defined chart-star family. -/
theorem exists_positive_integer_table_chartStar_ceiling_bound
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ r, HasChartStarRepresentation k r (fun z => (a z : ℂ)) →
        ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤ r) ∧
      ∀ i : Fin k,
        (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2 := by
  obtain ⟨a, ha, hbudget, hrank⟩ :=
    exists_positive_integer_table_obstructing_lowBudget_chartStars k hk
  exact ⟨a, ha, fun r hrep => natCeil_sqrt_lower_bound (hbudget r hrep), hrank⟩

/-- There is no uniform width bound for chart-star representations of all
positive-integer Boolean tables, even restricted to full flattening rank two. -/
theorem positive_integer_tables_require_unbounded_chartStar_width (B : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ a : BooleanTable k ℕ,
      (∀ z, 0 < a z) ∧
      (∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2) ∧
      ∀ r, HasChartStarRepresentation k r (fun z => (a z : ℂ)) → B < r := by
  obtain ⟨k, hk, hB⟩ := arbitrarily_large_required_width B
  obtain ⟨a, ha, hbudget, hrank⟩ :=
    exists_positive_integer_table_obstructing_lowBudget_chartStars k hk
  exact ⟨k, hk, a, ha, hrank, fun r hrep => hB r (hbudget r hrep)⟩

end
end MatchgateWidth
