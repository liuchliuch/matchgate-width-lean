import MatchgateWidth.ExactMatchgateLinear
import MatchgateWidth.LabelledInstances

/-!
# One common cover compresses the original labelled presentation

This constructs a presentation on exactly the original label types and domain.
The left tensors are unchanged and every induced right tensor is equal, including
zero tensors and nullary labels. No new labels or merged labels are used.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

namespace LabelledCommonPresentation
variable {S : LabelledShape} {E : Type} [Fintype E] {r t : ℕ}

/-- The presentation base with its matrix type made explicit. -/
def baseMatrix (p : LabelledCommonPresentation S E t) : Matrix E (BooleanInput t) ℂ := p.base

/-- A full-row exact common cover gives one smaller base for all original
labels, and equality of the induced labelled languages. -/
theorem compress_common_cover (p : LabelledCommonPresentation S E t)
    (P : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (hP : ExactMatchgateMatrix P) (hr : P.rank = 2 ^ r)
    (hcover : Submodule.span ℂ (Set.range p.base) ≤ orderedRowSpace P) :
    ∃ q : LabelledCommonPresentation S E r,
      p.baseMatrix = q.baseMatrix * P ∧ q.left = p.left ∧ q.language = p.language ∧
      (∀ l, q.rightPreimage l = blockwiseTransform P (S.rightArity l) (p.rightPreimage l)) := by
  obtain ⟨N, hN, hleft, hright⟩ := exact_labelwise_cover_compression p.base P hP hr hcover
  let q : LabelledCommonPresentation S E r := {
    base := N
    left := p.left
    rightPreimage := fun l => blockwiseTransform P (S.rightArity l) (p.rightPreimage l)
    validLeft := fun l => by
      apply (exactMatchgate_iff_booleanDiskRealizable _).mp
      exact hleft (S.leftArity l) (p.left l)
        ((exactMatchgate_iff_booleanDiskRealizable _).mpr (p.validLeft l))
    validRight := fun l => by
      apply (exactMatchgate_iff_booleanDiskRealizable _).mp
      exact (hright (S.rightArity l) (p.rightPreimage l)
        ((exactMatchgate_iff_booleanDiskRealizable _).mpr (p.validRight l))).1 }
  refine ⟨q, hN, rfl, ?_, fun _ => rfl⟩
  have hh : q.language.right = p.language.right := by
    funext l
    exact (hright (S.rightArity l) (p.rightPreimage l)
      ((exactMatchgate_iff_booleanDiskRealizable _).mpr (p.validRight l))).2.symm
  exact congrArg (LabelledLanguage.mk p.left) hh

/-- Equality is stronger than equivalence on the same ordered planar
instances; their vertices, incidences, arities and cyclic orders are retained. -/
theorem exactlyLabelledEquivalent_of_language_eq
    (p : LabelledCommonPresentation S E t) (q : LabelledCommonPresentation S E r)
    (h : q.language = p.language) : ExactlyLabelledEquivalent p.language q.language := by
  rw [h]
  exact ExactlyLabelledEquivalent.refl _

/-- Source common-cover compression with its exact-instance conclusion. -/
theorem exists_exactly_equivalent_of_common_cover (p : LabelledCommonPresentation S E t)
    (P : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (hP : ExactMatchgateMatrix P) (hr : P.rank = 2 ^ r)
    (hcover : Submodule.span ℂ (Set.range p.base) ≤ orderedRowSpace P) :
    ∃ q : LabelledCommonPresentation S E r,
      p.baseMatrix = q.baseMatrix * P ∧ q.left = p.left ∧ q.language = p.language ∧
      ExactlyLabelledEquivalent p.language q.language := by
  obtain ⟨q, hq, hl, he, _⟩ := p.compress_common_cover P hP hr hcover
  exact ⟨q, hq, hl, he, p.exactlyLabelledEquivalent_of_language_eq q he⟩

end LabelledCommonPresentation
end
end MatchgateWidth
