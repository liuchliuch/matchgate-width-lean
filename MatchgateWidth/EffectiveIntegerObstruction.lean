import MatchgateWidth.EffectivePolynomial
import MatchgateWidth.LabelledStarExtraction

/-!
# Effective search for the integer obstruction table

This implementation enumerates finite rational relation certificates, then
positive integer tables. All predicates executed by the search are decidable
rational arithmetic in `Effective.Polynomial`. The classical existence proofs
justify termination; they are erased and do not select any runtime witness.
No running-time, height, or bit-length bound is asserted.
-/

namespace MatchgateWidth.Effective

/-- The finite star sum with explicitly computable finite-domain instances. -/
def chartStar {k r : ℕ} {R : Type} [CommRing R]
    (c : StarChartChoice k r) (a : StarChartParameter k r → R)
    (z : BooleanInput k) : R :=
  ∑ x : Fin k → BooleanInput r,
    pfaffianPivotChart c.2.1 c.2.2 (fun t => a (.inr t))
      (flattenBooleanBlocks x) *
    ∏ i, pfaffianPivotChart (c.1 (z i)).1 (c.1 (z i)).2
      (fun t => a (.inl (z i, t))) (x i)

theorem chartStar_eq {k r : ℕ} {R : Type} [CommRing R]
    (c : StarChartChoice k r) (a : StarChartParameter k r → R) :
    chartStar c a = sampledChartStar c a := by
  funext z
  exact (sampledChartStar_eq_sum c a z).symm

/-- Computable coordinate polynomials for every discrete chart. -/
def chartPolynomial {k r : ℕ} (c : StarChartChoice k r) (z : BooleanInput k) :
    Polynomial (StarChartParameter k r) := chartStar c Polynomial.X z

@[simp] theorem interpret_chartPolynomial {k r : ℕ}
    (c : StarChartChoice k r) (z : BooleanInput k) :
    Polynomial.interpret (chartPolynomial c z) = sampledChartStarPolynomial c z := by
  rw [chartPolynomial, chartStar_eq]
  change Polynomial.interpretHom (sampledChartStar c Polynomial.X z) = _
  rw [sampledChartStar_map]
  simp only [Polynomial.interpretHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Polynomial.interpret_X]
  rfl

/-- A finite rational certificate can be checked by exact polynomial arithmetic. -/
def IsRelation {k r : ℕ} (c : StarChartChoice k r)
    (q : Polynomial (BooleanInput k)) : Prop :=
  q ≠ 0 ∧ Polynomial.compose q (chartPolynomial c) = 0

instance {k r : ℕ} (c : StarChartChoice k r) : DecidablePred (IsRelation c) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_relation {k r : ℕ} (h : D k r < 2 ^ k) (c : StarChartChoice k r) :
    ∃ q, IsRelation c q := by
  have hc : Fintype.card (StarChartParameter k r) < Fintype.card (BooleanInput k) := by
    rw [card_starChartParameter, card_booleanInput]
    exact h
  obtain ⟨q, hq, hrel⟩ := exists_nonzero_polynomial_relation_fintype hc
    (sampledChartStarPolynomial c)
  refine ⟨Polynomial.ofPolynomial q, ?_, ?_⟩
  · intro hz
    have hh := congrArg Polynomial.interpret hz
    apply hq
    simpa using hh
  · apply Polynomial.interpret_injective
    simp only [Polynomial.interpret_compose, Polynomial.interpret_ofPolynomial,
      interpret_chartPolynomial, Polynomial.interpret_zero]
    exact hrel

/-- Enumerate rational certificates until exact substitution gives zero.
`Encodable.choose` is a terminating executable natural-number search, not
`Classical.choose`; `exists_relation` supplies only its termination proof. -/
def relation {k r : ℕ} (h : D k r < 2 ^ k) (c : StarChartChoice k r) :
    Polynomial (BooleanInput k) := Encodable.choose (exists_relation h c)

theorem relation_spec {k r : ℕ} (h : D k r < 2 ^ k) (c : StarChartChoice k r) :
    IsRelation c (relation h c) := Encodable.choose_spec (exists_relation h c)

/-- Exactly the finitely many low-budget widths and all their chart choices. -/
abbrev RelevantChart (k : ℕ) :=
  Σ r : {r // r ∈ lowBudgetFinset k}, StarChartChoice k r.val

def chartRelation (k : ℕ) (d : RelevantChart k) : Polynomial (BooleanInput k) :=
  relation (mem_lowBudgetFinset.mp d.1.property) d.2

/-- The fixed two-column flattening minor, computed in the sparse ring. -/
def minor {k : ℕ} (i : Fin k) : Polynomial (BooleanInput k) :=
  Polynomial.X (insertPort i 0 (fun _ => 0)) * Polynomial.X (insertPort i 1 (fun _ => 1)) -
    Polynomial.X (insertPort i 0 (fun _ => 1)) * Polynomial.X (insertPort i 1 (fun _ => 0))

@[simp] theorem interpret_minor {k : ℕ} (i : Fin k) :
    Polynomial.interpret (minor i) = booleanMinor ℚ i (fun _ => 0) (fun _ => 1) := by
  simp [minor, booleanMinor]

/-- All obstruction certificates and rank certificates, indexed by a finite type. -/
def certificates (k : ℕ) : RelevantChart k ⊕ Fin k → Polynomial (BooleanInput k) :=
  Sum.elim (chartRelation k) minor

theorem certificates_ne_zero (k : ℕ) (hk : 2 ≤ k) (j : RelevantChart k ⊕ Fin k) :
    Polynomial.interpret (certificates k j) ≠ 0 := by
  cases j with
  | inl d =>
      intro hz
      have hq := (relation_spec (mem_lowBudgetFinset.mp d.1.property) d.2).1
      exact hq (Polynomial.interpret_injective (hz.trans Polynomial.interpret_zero.symm))
  | inr i =>
      simpa [certificates] using booleanMinor_ne_zero (R := ℚ) i
        (constant_rest_assignments_ne hk)

/-- The stopping test contains only finite quantifiers and exact rational evaluation. -/
def GoodTable (k : ℕ) (a : BooleanTable k ℕ) : Prop :=
  (∀ z, 0 < a z) ∧ ∀ j : RelevantChart k ⊕ Fin k,
    Polynomial.eval₂ (RingHom.id ℚ) (fun z => (a z : ℚ)) (certificates k j) ≠ 0

instance (k : ℕ) : DecidablePred (GoodTable k) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_goodTable (k : ℕ) (hk : 2 ≤ k) : ∃ a, GoodTable k a := by
  obtain ⟨a, ha, h⟩ := exists_positive_nat_forall_eval_ne_zero_fintype
    (fun j => Polynomial.interpret (certificates k j)) (certificates_ne_zero k hk)
  refine ⟨a, ha, ?_⟩
  intro j
  rw [Polynomial.eval₂_eq]
  exact h j

/-- A uniform terminating algorithm producing the positive integer obstruction table. -/
def integerTable (k : ℕ) (hk : 2 ≤ k) : BooleanTable k ℕ :=
  Encodable.choose (exists_goodTable k hk)

theorem integerTable_spec (k : ℕ) (hk : 2 ≤ k) : GoodTable k (integerTable k hk) :=
  Encodable.choose_spec (exists_goodTable k hk)


/-- Avoidance of every certificate is preserved by the rational embedding in ℂ. -/
theorem GoodTable.complex_eval_ne_zero {k : ℕ} {a : BooleanTable k ℕ}
    (h : GoodTable k a) (j : RelevantChart k ⊕ Fin k) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) (fun z => (a z : ℂ))
      (Polynomial.interpret (certificates k j)) ≠ 0 := by
  intro hz
  apply h.2 j
  rw [Polynomial.eval₂_eq]
  apply (Rat.castHom ℂ).injective
  rw [map_zero, MvPolynomial.eval₂_comp_left]
  simpa only [RingHom.comp_id, Function.comp_def, map_natCast] using hz

/-- The generated table has the full one-versus-rest ranks stated in the paper. -/
theorem integerTable_rank (k : ℕ) (hk : 2 ≤ k) (i : Fin k) :
    (oneVsRestFlattening (fun z => (integerTable k hk z : ℂ)) i).rank = 2 := by
  apply rank_oneVsRestFlattening_eq_two_of_eval₂_minor_ne_zero
    (Rat.castHom ℂ) _ i (fun _ => 0) (fun _ => 1)
  simpa only [certificates, Sum.elim_inr, interpret_minor] using
    (integerTable_spec k hk).complex_eval_ne_zero (.inr i)

/-- The executable output excludes every low-budget chart-star representation,
including arbitrary complex parameters. -/
theorem integerTable_chart_budget (k : ℕ) (hk : 2 ≤ k) {r : ℕ}
    (hrep : HasChartStarRepresentation k r (fun z => (integerTable k hk z : ℂ))) :
    2 ^ k ≤ D k r := by
  by_contra hn
  have hlow : D k r < 2 ^ k := by omega
  obtain ⟨c, a, ha⟩ := hrep
  let d : RelevantChart k := ⟨⟨r, mem_lowBudgetFinset.mpr hlow⟩, c⟩
  let q := relation hlow c
  have hrel : MvPolynomial.aeval (sampledChartStarPolynomial c)
      (Polynomial.interpret q) = 0 := by
    have h := congrArg Polynomial.interpret (relation_spec hlow c).2
    simpa only [Polynomial.interpret_compose, interpret_chartPolynomial,
      Polynomial.interpret_zero] using h
  have hv := eval₂_polynomialMap_eq_zero_of_relation (Rat.castHom ℂ)
    (sampledChartStarPolynomial c) (Polynomial.interpret q) hrel a
  change MvPolynomial.eval₂ (Rat.castHom ℂ)
    (fun z => MvPolynomial.eval₂ (Rat.castHom ℂ) a (sampledChartStarPolynomial c z))
    (Polynomial.interpret q) = 0 at hv
  simp_rw [eval₂_sampledChartStarPolynomial] at hv
  change MvPolynomial.eval₂ (Rat.castHom ℂ) (sampledChartStar c a)
    (Polynomial.interpret q) = 0 at hv
  rw [ha] at hv
  exact (integerTable_spec k hk).complex_eval_ne_zero (.inl d) hv

/-- Source Remark 6.5: one uniform executable function of `k ≥ 2` returns
positive integers, full rank-two flattenings, and the actual MGI-star width
obstruction. Its unbounded certificate/table searches terminate by the proved
algebraic-dependence and positive-grid theorems. -/
theorem integerTable_correct (k : ℕ) (hk : 2 ≤ k) :
    (∀ z, 0 < integerTable k hk z) ∧
    (∀ r, HasMGIStarRepresentation k r (fun z => (integerTable k hk z : ℂ)) →
      2 ^ k ≤ D k r) ∧
    ∀ i : Fin k, (oneVsRestFlattening (fun z => (integerTable k hk z : ℂ)) i).rank = 2 := by
  exact ⟨(integerTable_spec k hk).1,
    fun _ h => integerTable_chart_budget k hk (mgiStarRepresentation_has_chart h),
    integerTable_rank k hk⟩


/-- A total uniform program whose only input is the arity. Small arities,
which are outside the source assertion, return the constant-one table. -/
def integerTableForArity (k : ℕ) : BooleanTable k ℕ :=
  if hk : 2 ≤ k then integerTable k hk else fun _ => 1

/-- Positivity also holds at the harmless small-arity fallback. -/
theorem integerTableForArity_positive (k : ℕ) : ∀ z, 0 < integerTableForArity k z := by
  by_cases hk : 2 ≤ k
  · simpa only [integerTableForArity, dite_eq_left hk] using (integerTable_spec k hk).1
  · simp [integerTableForArity, hk]

/-- The executable conclusion of source Remark 6.5, uniformly in arity. -/
theorem remark_6_5_effective_integer_obstruction (k : ℕ) (hk : 2 ≤ k) :
    (∀ z, 0 < integerTableForArity k z) ∧
    (∀ r, HasMGIStarRepresentation k r (fun z => (integerTableForArity k z : ℂ)) →
      2 ^ k ≤ D k r) ∧
    ∀ i : Fin k, (oneVsRestFlattening (fun z => (integerTableForArity k z : ℂ)) i).rank = 2 := by
  simpa only [integerTableForArity, dite_eq_left hk] using integerTable_correct k hk


/-- Closed-star observations over an arbitrary finite competitor domain obey
the same budget for the computed table. -/
theorem integerTable_closedStar_budget {E : Type*} [Fintype E]
    (k : ℕ) (hk : 2 ≤ k) {r : ℕ}
    (p : CommonBaseClosedStarPresentation E k r
      (fun z => (integerTableForArity k z : ℂ))) : 2 ^ k ≤ D k r :=
  (remark_6_5_effective_integer_obstruction k hk).2.1 r p.hasMGIStarRepresentation

/-- Exact labelled equivalence permits arbitrary finite competitor domains,
arbitrary complex bases and weights, and arity-preserving changes of shape. -/
theorem integerTable_exactCommonWidth_budget (k : ℕ) (hk : 2 ≤ k)
    (j : Fin k) {r : ℕ}
    (h : HasExactCommonWidth
      (controlledLabelledLanguage (fun z => (integerTableForArity k z : ℂ)) j) r) :
    2 ^ k ≤ D k r :=
  exactCommonWidth_budget _ j (remark_6_5_effective_integer_obstruction k hk).2.1 h

/-- The paper's integer-ceiling consequence holds for every exact competitor. -/
theorem integerTable_exactCommonWidth_ceiling (k : ℕ) (hk : 2 ≤ k)
    (j : Fin k) {r : ℕ}
    (h : HasExactCommonWidth
      (controlledLabelledLanguage (fun z => (integerTableForArity k z : ℂ)) j) r) :
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤ r :=
  natCeil_sqrt_lower_bound (integerTable_exactCommonWidth_budget k hk j h)

end MatchgateWidth.Effective
