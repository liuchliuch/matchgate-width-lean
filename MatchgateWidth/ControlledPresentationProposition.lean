import MatchgateWidth.AlgebraicQutritLanguage
import MatchgateWidth.PivotCircuitRealization

/-! # Proposition 8.1: actual rational controlled presentation

Every labelled Boolean component is supplied with an actual rational-edge graph
and ordered disk drawing. The domain tensor is the literal common-base right
transform; its full coordinate support and all four displayed values are proved.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Complete exact rational presentation and restriction, valid for every
nowhere-zero integer-valued rational hard table (hence for the selected table). -/
theorem controlled_rational_presentation_proposition {k : ℕ}
    (f : BooleanTable k ℚ) (hf : ∀ x, f x ≠ 0)
    (hint : ∀ x, ∃ n : ℤ, f x = n) (j : Fin k) :
    let R := rightTransform (controlledCoordinateBase (K := ℚ) k)
      (controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j)
    Fintype.card ControlledLanguageLabel = 5 ∧
    (controlledCoordinateBase (K := ℚ) k).rank = 3 ∧
    (controlledPhysicalOrder k).length = (k + 2) * (2 ^ k + 3) ∧
    (∀ l : ControlledLanguageLabel,
      ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
        (ext : Fin (controlledLanguageBooleanArity k l) → Fin v),
        Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = q) ∧
        ∀ y, deletionSignature G ext y =
          ((controlledLanguageBoolean f hf j l
            ((booleanWordEquiv _).symm y) : ℚ) : ℂ)) ∧
    R = controlledQutrit f j ∧
    (∀ a, ∃ n : ℤ, R a = n) ∧
    (∀ a, ((∃ i, a (Sum.inr i) = 1) ∨
      (a (Sum.inl 0) = 2 ∨ a (Sum.inl 1) = 2)) → R a = 0) ∧
    (∀ x, R (controlledQutritAssignment 0 0 x) = f x ∧
      R (controlledQutritAssignment 1 1 x) = hardControlWeight (x j) * f x ∧
      R (controlledQutritAssignment 0 1 x) = 0 ∧
      R (controlledQutritAssignment 1 0 x) = 0) := by
  dsimp only
  rw [controlledPhysicalSignature_boolean_rightTransform f hf j]
  refine ⟨controlledLanguageLabel_card, controlledCoordinateBase_rank k,
    controlledPhysicalOrder_length k, ?_, rfl,
    controlledQutrit_integer_coordinates f hint j, ?_, ?_⟩
  · intro l
    have hn : 0 < controlledLanguageBooleanArity k l := by
      cases l <;> simp only [controlledLanguageBooleanArity, controlledPhysicalOrder_length] <;>
        positivity
    exact (controlledLanguageBoolean_mgi f hf j l).rational_diskWitness hn
  · intro a h
    rcases h with ⟨i, hi⟩ | (h₀ | h₁)
    · have hbad : ¬ ∀ i, a (Sum.inr i) ≠ 1 := fun h => h i hi
      simp [controlledQutrit, hbad]
    · simp [controlledQutrit, h₀]
    · simp [controlledQutrit, h₁]
  · intro x
    exact ⟨controlledQutrit_00 f j x, controlledQutrit_11 f j x,
      controlledQutrit_01 f j x, controlledQutrit_10 f j x⟩

end
end MatchgateWidth
