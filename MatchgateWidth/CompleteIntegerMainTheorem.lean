import MatchgateWidth.IntegerMainSourceTheorem
import MatchgateWidth.AllLeftStructuralTrichotomy
import MatchgateWidth.AllLeftSubstitutionRouting
import MatchgateWidth.SmallWidthFlagExample

/-! # Complete integer main theorem and unbounded actual flag alternative
The actual ordered-graph substitution theorem now supplies every all-gadget
Boolean-core normal form, using one endpoint basis for the whole closure.
All earlier arithmetic, graph, rank, and unrestricted-minimum conclusions are
retained on the same integer table and rational presentation.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000

theorem integerRationalPresentation_left_deficient (k : ℕ) (hk : 2 ≤ k) :
    LeftPortDeficient (integerRationalPresentation k hk).language := by
  intro l j
  have h := (integerControlledLanguage_qualifies k hk).2.2.2.2.1 l j
  rw [← integerRationalPresentation_language k hk] at h
  have hc : Fintype.card (Fin 3) = 3 := rfl
  rw [hc] at h
  omega

theorem integerRationalPresentation_flag_normal_form (k : ℕ) (hk : 2 ≤ k) :
    AllLeftFlagNormalForm (integerRationalPresentation k hk)
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) :=
  allLeft_flag_normal_form_of_exactLifting (integerRationalPresentation k hk)
    (controlledLabelledBase_rank k)
    (integerRationalPresentation_left_deficient k hk)
    (allLeftExactLifting_of_full_rank (integerRationalPresentation k hk)
      (controlledLabelledBase_rank k))
    (integerRationalPresentation_flag k hk)

theorem integerRationalPresentation_flag_alternative (k : ℕ) (hk : 2 ≤ k) :
    AllLeftFlagAlternative (integerRationalPresentation k hk) :=
  ⟨_,_,integerRationalPresentation_flag k hk,
    integerRationalPresentation_flag_normal_form k hk⟩

theorem source_integer_main_theorem_complete
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) (k : ℕ) (hk : 2 ≤ k) :
    IntegerMainConclusions k hk ∧
    (booleanParity (controlledLabelledCode k 0) = 0 ∧
      booleanParity (controlledLabelledCode k 1) = 1 ∧
      booleanParity (controlledLabelledCode k 2) = 0) ∧
    RationalCoefficientPresentation (integerRationalPresentation k hk) ∧
    RationalGraphPresentation (integerRationalPresentation k hk) ∧
    (integerRationalPresentation k hk).baseMatrix.rank = 3 ∧
    (integerRationalPresentation k hk).language = integerControlledLanguage k hk ∧
    IntegerPositiveDeficient (integerRationalPresentation k hk).language ∧
    AllLeftMonomialFlag (integerRationalPresentation k hk)
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) ∧
    HasExactCommonWidthOn (C k) (integerControlledLanguage k hk) (integerSourceMinimum C k) ∧
    (∀ r, HasExactCommonWidthOn (C k) (integerControlledLanguage k hk) r →
      integerSourceMinimum C k ≤ r) ∧
    2 ^ k ≤ 2 * (1 + (integerSourceMinimum C k).choose 2) + 1 +
      (k * integerSourceMinimum C k).choose 2 ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      integerSourceMinimum C k ∧
    integerSourceMinimum C k ≤ 2 ^ k + 3 ∧
    AllLeftFlagNormalForm (integerRationalPresentation k hk)
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) ∧
    PaperOmega (fun k => (integerSourceMinimum C k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) := by
  have h := source_integer_main_theorem C hC k hk
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2,
    integerRationalPresentation_flag_normal_form k hk,integer_source_width_omega C hC⟩

/-- The unbounded-family clause of source 3.3 includes genuine alternative III,
full ranks/essentiality/coupling, and unrestricted exact instance-class minima. -/
theorem source_flag_alternative_unbounded
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) :
    (∀ k (hk : 2 ≤ k), IntegerMainConclusions k hk ∧
      AllLeftFlagAlternative (integerRationalPresentation k hk)) ∧
    PaperOmega (fun k => (integerSourceMinimum C k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ∧
    ∀ B, B < integerSourceMinimum C (4 * B + 8) :=
  ⟨fun k hk => ⟨integer_main_theorem k hk,
    integerRationalPresentation_flag_alternative k hk⟩,
    integer_source_width_omega C hC,integer_source_width_unbounded C hC⟩

/-- Source Remark 3.4 also has a fixed finite-width genuine alternative III
example retaining all the main family's surrounding hypotheses. -/
theorem small_integer_flag_alternative :
    IntegerMainConclusions 2 (by decide) ∧
    AllLeftFlagAlternative (integerRationalPresentation 2 (by decide)) ∧
    ∀ C : LabelledInstanceClass (starLanguageShape 4),
      HasExactCommonWidthOn C (integerRationalPresentation 2 (by decide)).language 7 :=
  ⟨integer_main_theorem 2 (by decide),
    integerRationalPresentation_flag_alternative 2 (by decide),small_integer_flag_width_on⟩

end
end MatchgateWidth
