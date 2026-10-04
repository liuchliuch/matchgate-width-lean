import MatchgateWidth.RationalPresentationGraphs
import MatchgateWidth.ControlledAllLeftFlag
import MatchgateWidth.ControlledFlagEvenRay
import MatchgateWidth.SourceSupportTrichotomy

/-! # Source Theorem 3.1 enumerated clauses and simultaneous flag supports

This partial source assembly uses the same integer table and the same rational common
presentation for all clauses. The source instance class is independent of
tensor values and may encompass every source planar embedding. No equality of
minima with a smaller geometric model is asserted or required.
The final source reference to alternative (III) also requires fixed-basis
Boolean-core normal forms for every nonzero all-left boundary. That additional
conclusion is assembled in CompleteIntegerMainTheorem; this earlier component
alone does not certify full source3.1.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- The very same rational presentation is in the source one-plane flag class. -/
theorem integerRationalPresentation_flag (k : ℕ) (hk : 2 ≤ k) :
    AllLeftMonomialFlag (integerRationalPresentation k hk)
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) := by
  unfold AllLeftMonomialFlag
  rw [integerRationalPresentation_language]
  change qutritCoordinatePlane 2 ∈ allLeftRealizedSupports
      (controlledLabelledLanguage (integerHardTableIn ℂ k) (integerControlPort k hk)) 2 ∧
    qutritCoordinateRay 2 ∈ allLeftRealizedSupports
      (controlledLabelledLanguage (integerHardTableIn ℂ k) (integerControlPort k hk)) 1 ∧
    ¬ qutritCoordinateRay (K := ℂ) 2 ≤ qutritCoordinatePlane 2 ∧
    allLeftRealizedSupports
      (controlledLabelledLanguage (integerHardTableIn ℂ k) (integerControlPort k hk)) 2 =
      {qutritCoordinatePlane 2} ∧
    allLeftRealizedSupports
      (controlledLabelledLanguage (integerHardTableIn ℂ k) (integerControlPort k hk)) 1 ⊆
      {primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) 0,
       primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) 1,
       qutritCoordinateRay 2}
  have hf := controlled_actual_monomial_flag (integerHardTableIn ℂ k) (integerControlPort k hk)
  exact ⟨controlledAllLeft_plane_mem _ _,controlledAllLeft_ray_mem _ _ 2,hf.2.2,hf.1,
    le_of_eq hf.2.1⟩

/-- The simultaneous enumerated source clauses and flag support pattern at
each `k ≥ 2`; the referenced all-gadget Boolean-core clause is supplied by CompleteIntegerMainTheorem. The actual
minimum exists, is attained, has the displayed rational upper bound, and obeys
the unrestricted lower bound on every larger planar-instance class. -/
theorem source_integer_main_theorem
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
    integerSourceMinimum C k ≤ 2 ^ k + 3 := by
  have hbounds := integer_source_minimum_bounds C hC k hk
  refine ⟨integer_main_theorem k hk,controlled_flag_code_parities k hk,
    integerRationalPresentation_rational k hk,
    integerRationalPresentation_rational_graphs k hk,controlledLabelledBase_rank k,
    integerRationalPresentation_language k hk,?_,integerRationalPresentation_flag k hk,
    integerSourceMinimum_spec C k hk,fun _ h => integerSourceMinimum_le C k hk h,
    hbounds.1,hbounds.2.1,hbounds.2.2⟩
  rw [integerRationalPresentation_language]
  exact integerControlledLanguage_qualifies k hk

/-- The flag, rank, essentiality and connected two-center properties coexist
with a genuinely unbounded source-minimum sequence. -/
theorem source_integer_flag_family_unbounded
    (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (hC : ∀ k, ContainsOrderedPlanar (C k)) :
    (∀ k (hk : 2 ≤ k), IntegerMainConclusions k hk ∧
      AllLeftMonomialFlag (integerRationalPresentation k hk)
        (qutritCoordinatePlane 2) (qutritCoordinateRay 2)) ∧
    PaperOmega (fun k => (integerSourceMinimum C k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ∧
    ∀ B, B < integerSourceMinimum C (4 * B + 8) :=
  ⟨fun k hk => ⟨integer_main_theorem k hk,integerRationalPresentation_flag k hk⟩,
    integer_source_width_omega C hC,integer_source_width_unbounded C hC⟩

end
end MatchgateWidth
