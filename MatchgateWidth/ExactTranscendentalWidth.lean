import MatchgateWidth.LabelledInstanceClasses
import MatchgateWidth.TranscendentalCompanionLowerBound
import MatchgateWidth.WidthAdmissibility

/-! # Full-family width bounds independent of embedding normalization
A stronger notion of exact equivalence only restricts the admissible widths.
These statements take its actual nonempty width sets, not the smaller model's
minimum, and derive all bounds from the explicitly drawn planar star tests.
-/
namespace MatchgateWidth
noncomputable section

/-- Corollary 9.1 for every stronger family of admissibility predicates. The
constructed common presentation supplies nonemptiness for source admissibility;
source all-instance equivalence implies the displayed weaker model by restriction
to its explicitly drawn instances. No equality between minima is used. -/
theorem transcendental_source_width_family
    (W : ℕ → ℕ → Prop) (hW : ∀ k, 2 ≤ k → ∃ r, W k r)
    (hmodel : ∀ k (hk : 2 ≤ k) r, W k r →
      HasExactCommonWidth (controlledLabelledLanguage (transcendentalTable k)
        ⟨0, by omega⟩) r) :
    (∀ k, 2 ≤ k → 2^k ≤ D k (admissibleWidthSequence W hW k) ∧
      ⌈Real.sqrt (((2 : ℝ)^k-3)/(1+(k : ℝ)^2/2))⌉₊ ≤ admissibleWidthSequence W hW k) ∧
    PaperOmega (fun k => (admissibleWidthSequence W hW k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ)/2)/(k : ℝ)) ∧
    (∀ B, B < admissibleWidthSequence W hW (4*B+8)) := by
  have hb : ∀ k, 2 ≤ k → ∀ r, W k r → 2^k ≤ D k r := by
    intro k hk r hr
    exact transcendental_companion_commonWidth_budget ⟨0,by omega⟩ (hmodel k hk r hr)
  exact ⟨admissibleWidthSequence_lower_bound W hW hb,
    admissibleWidthSequence_omega W hW hb,
    admissibleWidthSequence_unbounded W hW hb⟩

/-- The actual admissible widths for a chosen family of raw instance classes.
Only the two unused small parameters are excluded; no width is filtered. -/
def transcendentalClassWidthCriterion
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k+2))) (k r : ℕ) : Prop :=
  ∃ hk : 2 ≤ k, HasExactCommonWidthOn (C k)
    (controlledLabelledLanguage (transcendentalTable k) ⟨0,by omega⟩) r

theorem transcendentalClassWidthCriterion_nonempty
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k+2)))
    (k : ℕ) (hk : 2 ≤ k) : ∃ r, transcendentalClassWidthCriterion C k r := by
  refine ⟨2^k+3,hk,?_⟩
  exact controlledLabelledLanguage_hasExactCommonWidthOn (C k) _
    (transcendentalTable_ne_zero k) ⟨0,by omega⟩

/-- Corollary 9.1 for every class of source instances containing the explicitly
certified planar tests. Admissibility, finite-width witnesses and restriction
are all derived from the literal domain/label/presentation definitions. -/
theorem transcendental_companion_arbitrary_instance_class
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k+2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) :
    let W := transcendentalClassWidthCriterion C
    let hW := transcendentalClassWidthCriterion_nonempty C
    (∀ k, 2 ≤ k → 2^k ≤ D k (admissibleWidthSequence W hW k) ∧
      ⌈Real.sqrt (((2 : ℝ)^k-3)/(1+(k : ℝ)^2/2))⌉₊ ≤ admissibleWidthSequence W hW k) ∧
    PaperOmega (fun k => (admissibleWidthSequence W hW k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ)/2)/(k : ℝ)) ∧
    (∀ B, B < admissibleWidthSequence W hW (4*B+8)) := by
  apply transcendental_source_width_family
  intro k hk r hr
  obtain ⟨hk',hr⟩ := hr
  exact hr.restrict (hC k)

end
end MatchgateWidth
