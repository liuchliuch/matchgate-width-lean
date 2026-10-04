import MatchgateWidth.MatchgateIdentities
import MatchgateWidth.StarChartObstruction

/-!
# Integer obstruction for the actual matchgate-identity locus

This assembles the proved identities-to-Pfaffian charts and polynomial avoidance.
No chart-coverage or polynomial-independence assumption is supplied. The one
remaining interface before this is a theorem about the paper's *planar graph*
matchgates is necessity of the identities for those graph deletion signatures.
That interface is explicitly not assumed or asserted here.
-/

namespace MatchgateWidth

noncomputable section

/-- A sampled star with signatures satisfying the literal quadratic identities. -/
def HasMGIStarRepresentation (k r : ℕ) (f : BooleanTable k ℂ) : Prop :=
  ∃ g : Fin 2 → BooleanTable r ℂ, ∃ Q : BooleanTable (k * r) ℂ,
    (∀ b, BooleanMatchgateIdentities (g b)) ∧ BooleanMatchgateIdentities Q ∧
      ∀ z, f z = starContract (fun x => Q (flattenBooleanBlocks x))
        (fun i => g (z i))

/-- Actual quadratic identities suffice for coverage by the finite polynomial charts. -/
theorem mgiStarRepresentation_has_chart {k r : ℕ} {f : BooleanTable k ℂ}
    (hf : HasMGIStarRepresentation k r f) : HasChartStarRepresentation k r f := by
  classical
  obtain ⟨g, Q, hg, hQ, hrep⟩ := hf
  choose p a ha using fun b => (hg b).exists_pfaffianPivotChart
  obtain ⟨pQ, aQ, haQ⟩ := hQ.exists_pfaffianPivotChart
  refine ⟨(fun b => (p b, fun _ => 0), (pQ, fun _ => 0)),
    Sum.elim (fun bt => a bt.1 bt.2) aQ, ?_⟩
  funext z
  rw [hrep z]
  simp_rw [ha, haQ]
  rfl

/-- Positive-integer, full-flattening-rank obstruction for the genuine MGI locus.
The witnesses are constructed by the preceding polynomial-avoidance theorems. -/
theorem exists_positive_integer_MGI_obstruction (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ r, HasMGIStarRepresentation k r (fun z => (a z : ℂ)) → 2 ^ k ≤ D k r) ∧
      ∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2 := by
  obtain ⟨a, ha, hbudget, hrank⟩ :=
    exists_positive_integer_table_obstructing_lowBudget_chartStars k hk
  exact ⟨a, ha, fun r hrep => hbudget r (mgiStarRepresentation_has_chart hrep), hrank⟩

/-- The same unconditional arithmetic consequence for algebraically independent tables. -/
theorem algebraicIndependent_table_MGI_budget {k r : ℕ} (f : BooleanTable k ℂ)
    (hf : AlgebraicIndependent ℚ f) (hrep : HasMGIStarRepresentation k r f) :
    2 ^ k ≤ D k r :=
  algebraicIndependent_table_chartStar_budget f hf (mgiStarRepresentation_has_chart hrep)

/-- No constant bounds all exact MGI-star representations of positive tables. -/
theorem positive_integer_tables_require_unbounded_MGI_star_width (B : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ a : BooleanTable k ℕ,
      (∀ z, 0 < a z) ∧
      (∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2) ∧
      ∀ r, HasMGIStarRepresentation k r (fun z => (a z : ℂ)) → B < r := by
  obtain ⟨k, hk, a, ha, hrank, hwidth⟩ :=
    positive_integer_tables_require_unbounded_chartStar_width B
  exact ⟨k, hk, a, ha, hrank, fun r hrep => hwidth r (mgiStarRepresentation_has_chart hrep)⟩

end
end MatchgateWidth
