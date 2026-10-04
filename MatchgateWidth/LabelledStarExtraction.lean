import MatchgateWidth.LabelledStarInstances

/-!
# Extracting closed stars from exact labelled equivalence

The observational field in `CommonBaseClosedStarPresentation` is constructed
from equality on all finite ordered planar instances. Both source pin
contraction and the selected instance's planar/order witnesses are proved.
The competitor can have any finite nonempty domain, arbitrary complex
coefficients and arbitrary common base. No tensor equality, rank assumption,
normalization, gadget replacement or positive-width condition is used.

`ExactlyLabelledEquivalent` uses the explicit geometric model of
`LabelledInstances`. Equality on a broader source class of embedded planar
ordered instances implies the needed equality on this constructed subclass;
no converse normalization theorem is needed for this lower-bound direction.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- The three unary transforms of a graph-defined common presentation satisfy
literal MGI, including at width zero. This uses no unary rank condition. -/
theorem LabelledCommonPresentation.starUnary_mgi {n r : ℕ} {E : Type}
    [Fintype E] (p : LabelledCommonPresentation (starLanguageShape n) E r)
    (b : Fin 3) :
    BooleanMatchgateIdentities
      (unaryTransform p.base (fun d => p.left (Sum.inl b) (fun _ => d))) := by
  have h := ((p.validLeft (Sum.inl b)).matchgateIdentities).cast (one_mul r)
  rw [LabelledCommonPresentation.leftTransform_one_block] at h
  exact h

/-- The selected-star observational equality is a conclusion of exact labelled
equivalence, not a field or extra assumption about the competing tensors. -/
def exactEquivalence_closedStarPresentation {k r : ℕ} {T : LabelledShape}
    {E : Type} [Fintype E] (f : BooleanTable k ℂ) (j : Fin k)
    (p : LabelledCommonPresentation T E r)
    (h : ExactlyLabelledEquivalent (controlledLabelledLanguage f j) p.language) :
    CommonBaseClosedStarPresentation E k r f := by
  classical
  let hex := exactEquivalence_closedStarValues f j p.language h
  let e := Classical.choose hex
  have he := Classical.choose_spec hex
  let q := p.pullback e
  refine {
    base := q.base
    labels := fun b d => q.left (Sum.inl b) (fun _ => d)
    center := q.rightPreimage 0
    validUnary := q.starUnary_mgi
    validCenter := (q.validRight 0).matchgateIdentities
    observes := ?_ }
  intro z
  have hs := he z
  rw [← p.pullback_language e] at hs
  exact hs

/-- End-to-end extraction for arbitrary competing labels and finite domain.
Both fixed zero link leaves are contracted by the existing ordered theorem. -/
theorem exactEquivalence_hasMGIStarRepresentation {k r : ℕ} {T : LabelledShape}
    {E : Type} [Fintype E] (f : BooleanTable k ℂ) (j : Fin k)
    (p : LabelledCommonPresentation T E r)
    (h : ExactlyLabelledEquivalent (controlledLabelledLanguage f j) p.language) :
    HasMGIStarRepresentation k r f :=
  (exactEquivalence_closedStarPresentation f j p h).hasMGIStarRepresentation

/-- Every presentation appearing in the minimum-width quantifier satisfies the
hard-table parameter budget. This also covers width zero. -/
theorem exactCommonWidth_budget {k r : ℕ} (f : BooleanTable k ℂ) (j : Fin k)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s)
    (h : HasExactCommonWidth (controlledLabelledLanguage f j) r) : 2 ^ k ≤ D k r := by
  obtain ⟨E,hE,hNE,T,p,he⟩ := h
  exact hf r (exactEquivalence_hasMGIStarRepresentation f j p he)

/-- The minimum exists only under a finite-width witness; the lower bound then
follows from the actual minimizing presentation, with no extra assumptions. -/
theorem minimumExactCommonWidth_budget {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s)
    (h : ∃ r, HasExactCommonWidth (controlledLabelledLanguage f j) r) :
    2 ^ k ≤ D k (minimumExactCommonWidth (controlledLabelledLanguage f j) h) :=
  exactCommonWidth_budget f j hf (minimumExactCommonWidth_spec _ h)

/-- The natural-number ceiling statement for the geometric-model minimum. -/
theorem minimumExactCommonWidth_ceil_lower_bound {k : ℕ}
    (f : BooleanTable k ℂ) (j : Fin k)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s)
    (h : ∃ r, HasExactCommonWidth (controlledLabelledLanguage f j) r) :
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      minimumExactCommonWidth (controlledLabelledLanguage f j) h :=
  natCeil_sqrt_lower_bound (minimumExactCommonWidth_budget f j hf h)

end
end MatchgateWidth
