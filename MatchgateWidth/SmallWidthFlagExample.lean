import MatchgateWidth.IntegerMainSourceTheorem
import MatchgateWidth.ControlledAllLeftFlag
import MatchgateWidth.SourceSupportTrichotomy
import MatchgateWidth.LabelledInstanceClasses

/-! # The small-width flag assertion in source Remark 3.4
A concrete width-five qutrit presentation has an actual monomial-flag closure.
This does not assert a pointwise width classification of flag languages.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

def smallFlagTable : BooleanTable 1 ℂ := fun _ => 1

theorem smallFlagTable_ne_zero (x : BooleanInput 1) : smallFlagTable x ≠ 0 := by
  simp [smallFlagTable]

def smallFlagPresentation : LabelledCommonPresentation (starLanguageShape 3) (Fin 3) 5 :=
  controlledLabelledPresentation smallFlagTable smallFlagTable_ne_zero 0

theorem smallFlagPresentation_rank : smallFlagPresentation.baseMatrix.rank = 3 :=
  controlledLabelledBase_rank 1

/-- A flag presentation of bounded displayed width actually exists; its rays
and plane occur at genuine connected planar primitive gadgets. -/
theorem smallFlagPresentation_flag :
    AllLeftMonomialFlag smallFlagPresentation (qutritCoordinatePlane 2) (qutritCoordinateRay 2) := by
  unfold AllLeftMonomialFlag smallFlagPresentation
  rw [controlledLabelledPresentation_language]
  change qutritCoordinatePlane 2 ∈ allLeftRealizedSupports
      (controlledLabelledLanguage smallFlagTable 0) 2 ∧
    qutritCoordinateRay 2 ∈ allLeftRealizedSupports
      (controlledLabelledLanguage smallFlagTable 0) 1 ∧
    ¬ qutritCoordinateRay (K := ℂ) 2 ≤ qutritCoordinatePlane 2 ∧
    allLeftRealizedSupports (controlledLabelledLanguage smallFlagTable 0) 2 =
      {qutritCoordinatePlane 2} ∧
    allLeftRealizedSupports (controlledLabelledLanguage smallFlagTable 0) 1 ⊆
      {primitiveParityEndpoint (controlledLabelledBase 1) (qutritCoordinatePlane 2) 0,
       primitiveParityEndpoint (controlledLabelledBase 1) (qutritCoordinatePlane 2) 1,
       qutritCoordinateRay 2}
  have hf := controlled_actual_monomial_flag smallFlagTable (0 : Fin 1)
  exact ⟨controlledAllLeft_plane_mem _ _,controlledAllLeft_ray_mem _ _ 2,
    hf.2.2,hf.1,le_of_eq hf.2.1⟩

/-- The same language has width at most five on every chosen instance class,
without assuming a smaller-model minimum equals a larger-model minimum. -/
theorem smallFlagPresentation_width_on (C : LabelledInstanceClass (starLanguageShape 3)) :
    HasExactCommonWidthOn C smallFlagPresentation.language 5 := by
  exact ⟨Fin 3,inferInstance,inferInstance,starLanguageShape 3,smallFlagPresentation,
    ExactlyLabelledEquivalentOn.refl C _⟩

theorem smallFlagPresentation_minimum_le_five
    (C : LabelledInstanceClass (starLanguageShape 3)) :
    let h := (show ∃ r, HasExactCommonWidthOn C smallFlagPresentation.language r from
      ⟨5,smallFlagPresentation_width_on C⟩)
    Nat.find h ≤ 5 := Nat.find_min' _ (smallFlagPresentation_width_on C)

/-- A fixed width-seven example also retains every established integer-family
rank, support-essentiality, positivity and connected-coupling property. -/
theorem small_integer_flag_example :
    IntegerMainConclusions 2 (by decide) ∧
    (integerRationalPresentation 2 (by decide)).baseMatrix.rank=3 ∧
    RationalGraphPresentation (integerRationalPresentation 2 (by decide)) ∧
    IntegerPositiveDeficient (integerRationalPresentation 2 (by decide)).language ∧
    AllLeftMonomialFlag (integerRationalPresentation 2 (by decide))
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) := by
  refine ⟨integer_main_theorem 2 (by decide),controlledLabelledBase_rank 2,
    integerRationalPresentation_rational_graphs 2 (by decide),?_,
    integerRationalPresentation_flag 2 (by decide)⟩
  rw [integerRationalPresentation_language]
  exact integerControlledLanguage_qualifies 2 (by decide)

theorem small_integer_flag_width_on
    (C : LabelledInstanceClass (starLanguageShape 4)) :
    HasExactCommonWidthOn C (integerRationalPresentation 2 (by decide)).language 7 := by
  exact ⟨Fin 3,inferInstance,inferInstance,starLanguageShape 4,
    integerRationalPresentation 2 (by decide),ExactlyLabelledEquivalentOn.refl C _⟩

end
end MatchgateWidth
