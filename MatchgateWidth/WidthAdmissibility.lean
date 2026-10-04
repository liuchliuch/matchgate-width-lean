import MatchgateWidth.WidthAsymptotics

/-! # Minimum widths for any stronger source admissibility notion

The arithmetic conclusions require only nonempty admissible-width sets and
that every admissible width satisfies the parameter budget. In applications
`W k r` can quantify over the paper's full planar-instance class. There is no
claim that its minimum equals the minimum of a smaller formal instance model.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- The least admissible width for every source parameter `k ≥ 2`. The two
unused indices are set to zero only to give an ordinary natural sequence. -/
def admissibleWidthSequence (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r) (k : ℕ) : ℕ :=
  if hk : 2 ≤ k then Nat.find (hW k hk) else 0

theorem admissibleWidthSequence_spec (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r) (k : ℕ) (hk : 2 ≤ k) :
    W k (admissibleWidthSequence W hW k) := by
  simpa only [admissibleWidthSequence, dite_eq_left hk] using Nat.find_spec (hW k hk)

theorem admissibleWidthSequence_le (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r) (k : ℕ) (hk : 2 ≤ k)
    {r : ℕ} (hr : W k r) : admissibleWidthSequence W hW k ≤ r := by
  simpa only [admissibleWidthSequence, dite_eq_left hk] using Nat.find_min' (hW k hk) hr

/-- Budget and ceiling bound for the true minimum of the chosen criterion. -/
theorem admissibleWidthSequence_lower_bound (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r)
    (hbudget : ∀ k, 2 ≤ k → ∀ r, W k r → 2 ^ k ≤ D k r)
    (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k ≤ D k (admissibleWidthSequence W hW k) ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      admissibleWidthSequence W hW k := by
  have hb := hbudget k hk _ (admissibleWidthSequence_spec W hW k hk)
  exact ⟨hb, natCeil_sqrt_lower_bound hb⟩

/-- The asymptotic lower bound for any such source-level minimum. -/
theorem admissibleWidthSequence_omega (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r)
    (hbudget : ∀ k, 2 ≤ k → ∀ r, W k r → 2 ^ k ≤ D k r) :
    PaperOmega (fun k => (admissibleWidthSequence W hW k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) :=
  paperOmega_widths_of_budget _ fun k hk =>
    (admissibleWidthSequence_lower_bound W hW hbudget k hk).1

theorem admissibleWidthSequence_scale_isBigO (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r)
    (hbudget : ∀ k, 2 ≤ k → ∀ r, W k r → 2 ^ k ≤ D k r) :
    Asymptotics.IsBigO Filter.atTop
      (fun k : ℕ => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ))
      (fun k => (admissibleWidthSequence W hW k : ℝ)) :=
  (paperOmega_iff_isBigO _ _).mp (admissibleWidthSequence_omega W hW hbudget)

/-- An explicit parameter defeats any proposed fixed width bound. -/
theorem admissibleWidthSequence_unbounded (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r)
    (hbudget : ∀ k, 2 ≤ k → ∀ r, W k r → 2 ^ k ≤ D k r) (B : ℕ) :
    B < admissibleWidthSequence W hW (4 * B + 8) := by
  have hb := (admissibleWidthSequence_lower_bound W hW hbudget (4 * B + 8)
    (by omega)).1
  have hx := budget_lt_two_pow_at_explicit_arity B
  by_contra hn
  have hm := D_mono_width (4 * B + 8) (Nat.le_of_not_gt hn)
  omega

/-- On a constant domain of size three, no domain-cardinality function can
bound the minima of a family obeying these budgets. -/
theorem no_domain_cardinality_bound_of_budgets (W : ℕ → ℕ → Prop)
    (hW : ∀ k, 2 ≤ k → ∃ r, W k r)
    (hbudget : ∀ k, 2 ≤ k → ∀ r, W k r → 2 ^ k ≤ D k r) :
    ¬ ∃ h : ℕ → ℕ, ∀ k, 2 ≤ k → admissibleWidthSequence W hW k ≤ h 3 := by
  rintro ⟨h,hh⟩
  exact (not_le_of_gt (admissibleWidthSequence_unbounded W hW hbudget (h 3)))
    (hh (4 * h 3 + 8) (by omega))

end
end MatchgateWidth
