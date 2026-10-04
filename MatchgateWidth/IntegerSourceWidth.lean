import MatchgateWidth.IntegerMainTheorem
import MatchgateWidth.LabelledInstanceClasses

/-! # Main integer family on every encompassing source instance class

The class argument specifies actual labelled incidence instances independently
of tensor values. It may be the full source planar class. Only inclusion of
the already drawn ordered planar stars is needed for the lower bound. The
literal self-presentation establishes finiteness for every class, without a
normalization theorem and without assuming existence of a minimum.
-/
namespace MatchgateWidth
noncomputable section

/-- Exact-width admissibility on the chosen source class. -/
def integerSourceWidths
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2))) (k r : ℕ) : Prop :=
  ∃ hk : 2 ≤ k, HasExactCommonWidthOn (C k) (integerControlledLanguage k hk) r

theorem integerSourceWidths_finite
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (k : ℕ) (hk : 2 ≤ k) : ∃ r, integerSourceWidths C k r := by
  refine ⟨2 ^ k + 3,hk,?_⟩
  exact controlledLabelledLanguage_hasExactCommonWidthOn (C k) (integerHardTableIn ℂ k)
    (integerHardTableIn_ne_zero ℂ k) (integerControlPort k hk)

/-- The source minimum includes arbitrary finite competitor domains, arbitrary
complex bases and weights, and arity-preserving changes of the labelled shape. -/
def integerSourceMinimum
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2))) : ℕ → ℕ :=
  admissibleWidthSequence (integerSourceWidths C) (integerSourceWidths_finite C)

theorem integerSourceMinimum_spec
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (k : ℕ) (hk : 2 ≤ k) :
    HasExactCommonWidthOn (C k) (integerControlledLanguage k hk) (integerSourceMinimum C k) := by
  obtain ⟨_,h⟩ := admissibleWidthSequence_spec (integerSourceWidths C)
    (integerSourceWidths_finite C) k hk
  exact h

theorem integerSourceMinimum_le
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (k : ℕ) (hk : 2 ≤ k) {r : ℕ}
    (hr : HasExactCommonWidthOn (C k) (integerControlledLanguage k hk) r) :
    integerSourceMinimum C k ≤ r :=
  admissibleWidthSequence_le (integerSourceWidths C) (integerSourceWidths_finite C) k hk ⟨hk,hr⟩

theorem integerSourceWidths_budget
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k))
    (k : ℕ) (hk : 2 ≤ k) (r : ℕ) (hr : integerSourceWidths C k r) :
    2 ^ k ≤ D k r := by
  obtain ⟨_,hr⟩ := hr
  exact integer_main_width_budget k hk (hr.restrict (hC k))

/-- The complete source budget, exact ceiling, and constructed upper bound. -/
theorem integer_source_minimum_bounds
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k ≤ 2 * (1 + (integerSourceMinimum C k).choose 2) + 1 +
      (k * integerSourceMinimum C k).choose 2 ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      integerSourceMinimum C k ∧
    integerSourceMinimum C k ≤ 2 ^ k + 3 := by
  have h := admissibleWidthSequence_lower_bound (integerSourceWidths C)
    (integerSourceWidths_finite C) (integerSourceWidths_budget C hC) k hk
  refine ⟨?_,h.2,?_⟩
  · simpa only [integerSourceMinimum,D,delta,Nat.add_assoc] using h.1
  · exact integerSourceMinimum_le C k hk
      (controlledLabelledLanguage_hasExactCommonWidthOn (C k) (integerHardTableIn ℂ k)
        (integerHardTableIn_ne_zero ℂ k) (integerControlPort k hk))

theorem integer_source_width_omega
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) :
    PaperOmega (fun k => (integerSourceMinimum C k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) :=
  admissibleWidthSequence_omega (integerSourceWidths C) (integerSourceWidths_finite C)
    (integerSourceWidths_budget C hC)

theorem integer_source_width_unbounded
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) (B : ℕ) :
    B < integerSourceMinimum C (4 * B + 8) :=
  admissibleWidthSequence_unbounded (integerSourceWidths C) (integerSourceWidths_finite C)
    (integerSourceWidths_budget C hC) B

/-- Source Corollary 3.2: even on the constant domain of cardinality three,
the integer rationally-presented family defeats every cardinality bound. -/
theorem integer_source_no_domain_bound
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) :
    ¬ ∃ h : ℕ → ℕ, ∀ k, 2 ≤ k → integerSourceMinimum C k ≤ h 3 :=
  no_domain_cardinality_bound_of_budgets (integerSourceWidths C)
    (integerSourceWidths_finite C) (integerSourceWidths_budget C hC)

end
end MatchgateWidth
