import MatchgateWidth.ControlledLabelledPresentation
import MatchgateWidth.LabelledStarExtraction

/-! # Exact labelled equivalence on arbitrary classes of raw ordered instances
The class is independent of tensor values. It may encode a larger notion of
planar embedding than the explicit drawings used for the test instances.
Self-presentations are valid for every class, while restricting equivalence
along class inclusion gives the extraction theorem without normalizing drawings.
-/
namespace MatchgateWidth
noncomputable section

abbrev LabelledInstanceClass (S : LabelledShape) :=
  ∀ (a b c : ℕ), LabelledInstance S a b c → Prop

def ContainsOrderedPlanar {S : LabelledShape} (C : LabelledInstanceClass S) : Prop :=
  ∀ a b c (I : LabelledInstance S a b c), Nonempty I.OrderedPlanar → C a b c I

def ExactlyLabelledEquivalentOn {S T : LabelledShape} {D E : Type}
    [Fintype D] [Fintype E] (C : LabelledInstanceClass S)
    (F : LabelledLanguage S D) (G : LabelledLanguage T E) : Prop :=
  ∃ e : LabelledShapeEquiv S T, ∀ a b c (I : LabelledInstance S a b c),
    C a b c I → I.value F = I.value (e.pullback G)

theorem ExactlyLabelledEquivalentOn.refl {S : LabelledShape} {D : Type}
    [Fintype D] (C : LabelledInstanceClass S) (F : LabelledLanguage S D) :
    ExactlyLabelledEquivalentOn C F F := by
  refine ⟨LabelledShapeEquiv.refl S, ?_⟩
  intro a b c I hI
  simp

theorem ExactlyLabelledEquivalentOn.restrict {S T : LabelledShape} {D E : Type}
    [Fintype D] [Fintype E] {C : LabelledInstanceClass S}
    {F : LabelledLanguage S D} {G : LabelledLanguage T E}
    (h : ExactlyLabelledEquivalentOn C F G) (hC : ContainsOrderedPlanar C) :
    ExactlyLabelledEquivalent F G := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,fun a b c I hI => he a b c I (hC a b c I hI)⟩

def HasExactCommonWidthOn {S : LabelledShape} {D : Type} [Fintype D]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D) (r : ℕ) : Prop :=
  ∃ (E : Type) (_ : Fintype E) (_ : Nonempty E) (T : LabelledShape)
    (p : LabelledCommonPresentation T E r), ExactlyLabelledEquivalentOn C F p.language

theorem HasExactCommonWidthOn.restrict {S : LabelledShape} {D : Type} [Fintype D]
    {C : LabelledInstanceClass S} {F : LabelledLanguage S D} {r : ℕ}
    (h : HasExactCommonWidthOn C F r) (hC : ContainsOrderedPlanar C) :
    HasExactCommonWidth F r := by
  obtain ⟨E,hE,hNE,T,p,he⟩ := h
  exact ⟨E,hE,hNE,T,p,he.restrict hC⟩

/-- Actual self-presentation proves admissibility on every instance class,
with no containment or embedding assumption. -/
theorem controlledLabelledLanguage_hasExactCommonWidthOn {k : ℕ}
    (C : LabelledInstanceClass (starLanguageShape (k+2)))
    (f : BooleanTable k ℂ) (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    HasExactCommonWidthOn C (controlledLabelledLanguage f j) (2^k+3) := by
  refine ⟨Fin 3,inferInstance,inferInstance,starLanguageShape (k+2),
    controlledLabelledPresentation f hf j,?_⟩
  rw [controlledLabelledPresentation_language]
  exact ExactlyLabelledEquivalentOn.refl C _

/-- Every competing domain, label set and base is handled by actual closed
star extraction after restriction. The class itself is unrelated to values. -/
theorem exactCommonWidthOn_budget {k r : ℕ}
    (C : LabelledInstanceClass (starLanguageShape (k+2)))
    (hC : ContainsOrderedPlanar C) (f : BooleanTable k ℂ) (j : Fin k)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2^k ≤ D k s)
    (h : HasExactCommonWidthOn C (controlledLabelledLanguage f j) r) :
    2^k ≤ D k r := exactCommonWidth_budget f j hf (h.restrict hC)

end
end MatchgateWidth
