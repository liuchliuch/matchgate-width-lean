import MatchgateWidth.WidthBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The exponential-over-linear width lower bound

This is the exact arithmetic layer of the paper's `Ω(2^(k/2)/k)` statement.
Every conclusion is conditional on the explicit parameter-budget inequality
`2 ^ k ≤ D k r`; this file does not establish that inequality for any matchgate
presentation or assert a representation-theoretic width theorem.
-/

namespace MatchgateWidth

/-- Converting the square root of a natural power to the real exponent in the paper. -/
theorem sqrt_two_pow_eq_rpow (k : ℕ) :
    Real.sqrt ((2 : ℝ) ^ k) = Real.rpow 2 ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- An explicit lower bound valid from arity two, with constant `1/2`. -/
theorem half_sqrt_two_pow_div_le_width {k r : ℕ} (hk : 2 ≤ k)
    (hbudget : 2 ^ k ≤ D k r) :
    (1 / 2 : ℝ) * Real.sqrt ((2 : ℝ) ^ k) / (k : ℝ) ≤ (r : ℝ) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hpowNat : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hpowNat
  have hden : 1 + (k : ℝ) ^ 2 / 2 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hupper : (2 : ℝ) ^ k - 3 ≤ (r : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
    calc
      (2 : ℝ) ^ k - 3 ≤ (r : ℝ) ^ 2 * (1 + (k : ℝ) ^ 2 / 2) :=
        (readable_inequality hbudget).1.trans (readable_inequality hbudget).2
      _ ≤ (r : ℝ) ^ 2 * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hden (sq_nonneg _)
  have hsq : (2 : ℝ) ^ k ≤ (2 * (k : ℝ) * (r : ℝ)) ^ 2 := by
    nlinarith only [hpow, hupper]
  have hsqrt : Real.sqrt ((2 : ℝ) ^ k) ≤ 2 * (k : ℝ) * (r : ℝ) :=
    (Real.sqrt_le_left (by positivity)).mpr hsq
  apply (div_le_iff₀ hkpos).mpr
  nlinarith only [hsqrt]

/-- The paper's exact scale, with a concrete positive constant and threshold. -/
theorem half_rpow_div_le_width {k r : ℕ} (hk : 2 ≤ k)
    (hbudget : 2 ^ k ≤ D k r) :
    (1 / 2 : ℝ) * (Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ≤ (r : ℝ) := by
  simpa only [sqrt_two_pow_eq_rpow, mul_div_assoc] using
    half_sqrt_two_pow_div_le_width hk hbudget

/-- The existential constant-and-threshold definition of `Ω` used in the paper.
The functions are real-valued and the parameter is a natural-number arity. -/
def PaperOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → c * |g k| ≤ |f k|

/-- Any natural-valued width sequence obeying the budgets has the paper's exact
`Ω(2^(k/2)/k)` lower bound.  The witnesses are `c = 1/2` and `k₀ = 2`. -/
theorem paperOmega_widths_of_budget (width : ℕ → ℕ)
    (hbudget : ∀ k : ℕ, 2 ≤ k → 2 ^ k ≤ D k (width k)) :
    PaperOmega (fun k => (width k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) := by
  refine ⟨1 / 2, by norm_num, 2, ?_⟩
  intro k hk
  change (1 / 2 : ℝ) * |Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)| ≤ |(width k : ℝ)|
  have hscale : 0 ≤ Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg k)
  rw [abs_of_nonneg hscale, abs_of_nonneg (Nat.cast_nonneg (width k))]
  exact half_rpow_div_le_width hk (hbudget k hk)

/-- The asymptotic conclusion without any custom asymptotic notation. -/
theorem exists_omega_constants_of_budget (width : ℕ → ℕ)
    (hbudget : ∀ k : ℕ, 2 ≤ k → 2 ^ k ≤ D k (width k)) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      |(width k : ℝ)| ≥ c * |Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)| :=
  paperOmega_widths_of_budget width hbudget

/-- The explicit paper definition agrees with Mathlib's standard upper-bound
relation, with the arguments reversed. -/
theorem paperOmega_iff_isBigO (f g : ℕ → ℝ) :
    PaperOmega f g ↔ Asymptotics.IsBigO Filter.atTop g f := by
  rw [Asymptotics.isBigO_iff'']
  simp only [PaperOmega, Filter.eventually_atTop, Real.norm_eq_abs]

/-- Standard Mathlib formulation: the target exponential-over-linear scale is
`O(width)`, which says exactly that `width` is `Ω` of that scale. -/
theorem scale_isBigO_widths_of_budget (width : ℕ → ℕ)
    (hbudget : ∀ k : ℕ, 2 ≤ k → 2 ^ k ≤ D k (width k)) :
    Asymptotics.IsBigO Filter.atTop
      (fun k : ℕ => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ))
      (fun k : ℕ => (width k : ℝ)) :=
  (paperOmega_iff_isBigO _ _).mp (paperOmega_widths_of_budget width hbudget)

end MatchgateWidth
