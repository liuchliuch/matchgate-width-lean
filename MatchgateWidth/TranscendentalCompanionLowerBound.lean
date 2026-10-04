import MatchgateWidth.TranscendentalCompanionPresentation
import MatchgateWidth.ControlledLabelledPresentation
import MatchgateWidth.LabelledStarExtraction

/-! # Corollary 9.1: unrestricted exact re-presentation of the closed-form companion

The lower bound only uses closed labelled planar stars. Thus it already follows
from equality on the explicit ordered planar instance model and applies, a
fortiori, when equivalence is required on every source planar instance. No
normalization of general planar embeddings or equality of the two minima is
claimed. A generic admissibility-predicate version makes that distinction explicit.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Corollary 9.1's precise parameter budget, with arbitrary finite competitor
domain, arbitrary labelled shape, arbitrary complex base and weights, and every
nonnegative width. Nothing is imposed on the competitor's rank or normalization. -/
theorem transcendental_companion_exact_bound {k r : ℕ} {T : LabelledShape}
    {E : Type} [Fintype E] (j : Fin k)
    (p : LabelledCommonPresentation T E r)
    (h : ExactlyLabelledEquivalent
      (controlledLabelledLanguage (transcendentalTable k) j) p.language) :
    2 ^ k ≤ 2 * delta r + delta (k * r) :=
  transcendentalTable_MGI_budget k r
    (exactEquivalence_hasMGIStarRepresentation (transcendentalTable k) j p h)

/-- The exact lower bound for every admissible width in the geometric model. -/
theorem transcendental_companion_commonWidth_budget {k r : ℕ} (j : Fin k)
    (h : HasExactCommonWidth (controlledLabelledLanguage (transcendentalTable k) j) r) :
    2 ^ k ≤ D k r :=
  exactCommonWidth_budget (transcendentalTable k) j (transcendentalTable_MGI_budget k) h

/-- The minimum-width budget for any stronger admissibility notion. In
particular one can require equality on a larger class of planar instances;
only its implication to the proved star-extraction model is needed. -/
theorem transcendental_companion_admissible_minimum_bound {k : ℕ} (j : Fin k)
    (W : ℕ → Prop) (hW : ∃ r, W r)
    (hmodel : ∀ r, W r →
      HasExactCommonWidth (controlledLabelledLanguage (transcendentalTable k) j) r) :
    2 ^ k ≤ 2 * delta (Nat.find hW) + delta (k * Nat.find hW) ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤ Nat.find hW := by
  have hb := transcendental_companion_commonWidth_budget j (hmodel _ (Nat.find_spec hW))
  exact ⟨hb, natCeil_sqrt_lower_bound hb⟩

/-- The actual minimum in the geometric labelled-instance model. Its existence
is proved by the constructed controlled common-base presentation. -/
def transcendentalCompanionMinimum (k : ℕ) (j : Fin k) : ℕ :=
  minimumExactCommonWidth (controlledLabelledLanguage (transcendentalTable k) j)
    (controlledLabelledLanguage_finiteWidth (transcendentalTable k)
      (transcendentalTable_ne_zero k) j)

/-- The minimum's budget and the source's exact ceiling lower bound. -/
theorem transcendental_companion_minimum_lower_bound (k : ℕ) (j : Fin k) :
    2 ^ k ≤ 2 * delta (transcendentalCompanionMinimum k j) +
      delta (k * transcendentalCompanionMinimum k j) ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      transcendentalCompanionMinimum k j := by
  have hb := minimumExactCommonWidth_budget (transcendentalTable k) j
    (transcendentalTable_MGI_budget k)
    (controlledLabelledLanguage_finiteWidth (transcendentalTable k)
      (transcendentalTable_ne_zero k) j)
  exact ⟨hb, natCeil_sqrt_lower_bound hb⟩

/-- For an ordinary natural-indexed width sequence, choose the first hard port
when one exists; the arbitrary arity-zero value is irrelevant asymptotically. -/
def transcendentalCompanionWidth (k : ℕ) : ℕ :=
  if hk : 0 < k then transcendentalCompanionMinimum k ⟨0,hk⟩ else 0

theorem transcendentalCompanionWidth_budget (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k ≤ D k (transcendentalCompanionWidth k) := by
  have hp : 0 < k := by omega
  simpa only [transcendentalCompanionWidth, dite_eq_left hp, D] using
    (transcendental_companion_minimum_lower_bound k ⟨0,hp⟩).1

/-- The precise `Omega(2^(k/2)/k)` conclusion, with proved finite minima. -/
theorem transcendental_companion_width_omega :
    PaperOmega (fun k => (transcendentalCompanionWidth k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) :=
  paperOmega_widths_of_budget transcendentalCompanionWidth transcendentalCompanionWidth_budget

/-- Standard Mathlib asymptotics for the same sequence. -/
theorem transcendental_companion_scale_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun k : ℕ => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ))
      (fun k => (transcendentalCompanionWidth k : ℝ)) :=
  scale_isBigO_widths_of_budget transcendentalCompanionWidth transcendentalCompanionWidth_budget

/-- A concrete closed-form witness beats every proposed fixed width bound. -/
theorem transcendental_companion_unbounded (B : ℕ) :
    B < transcendentalCompanionWidth (4 * B + 8) := by
  have hb := transcendentalCompanionWidth_budget (4 * B + 8) (by omega)
  have hx := budget_lt_two_pow_at_explicit_arity B
  by_contra hn
  have hm := D_mono_width (4 * B + 8) (Nat.le_of_not_gt hn)
  omega

end
end MatchgateWidth
