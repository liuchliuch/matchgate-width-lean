import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter budgets and quantitative consequences

This file proves the arithmetic deductions used in Proposition 6.4 and Section 9 of
arXiv:2610.00079v1.  The hypothesis `2 ^ k ≤ D k r` is an explicit input: deriving
that hypothesis from arbitrary matchgate presentations is outside these arithmetic
lemmas.
-/

namespace MatchgateWidth

/-- The parameter budget for an `n`-external matchgate chart. -/
def delta (n : ℕ) : ℕ := 1 + n.choose 2

/-- The budget for two width-`r` samplers and a `k*r`-external central tensor. -/
def D (k r : ℕ) : ℕ := 2 * delta r + delta (k * r)

@[simp] theorem delta_zero : delta 0 = 1 := by simp [delta]

@[simp] theorem D_zero (k : ℕ) : D k 0 = 3 := by simp [D]

theorem delta_succ (n : ℕ) : delta (n + 1) = delta n + n := by
  simp [delta, Nat.choose_succ_succ, Nat.choose_one_right]
  omega

/-- A simple coercive bound sufficient to make every sublevel set finite. -/
theorem le_delta (n : ℕ) : n ≤ delta n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [delta_succ]
    cases n with
    | zero => simp
    | succ n => omega

theorem le_D (k r : ℕ) : r ≤ D k r := by
  have h := le_delta r
  unfold D
  omega

/-- The set `R_k` used in the positive-integer obstruction argument. -/
def lowBudgetWidths (k : ℕ) : Set ℕ := {r | D k r < 2 ^ k}

theorem lowBudgetWidths_bounded (k : ℕ) :
    lowBudgetWidths k ⊆ ↑(Finset.range (2 ^ k)) := by
  intro r hr
  exact Finset.mem_range.mpr (lt_of_le_of_lt (le_D k r) hr)

theorem lowBudgetWidths_finite (k : ℕ) : (lowBudgetWidths k).Finite :=
  (Finset.finite_toSet _).subset (lowBudgetWidths_bounded k)

/-- A computable finite enumeration of the same low-budget widths. -/
def lowBudgetFinset (k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ k)).filter (fun r => D k r < 2 ^ k)

@[simp] theorem mem_lowBudgetFinset {k r : ℕ} :
    r ∈ lowBudgetFinset k ↔ D k r < 2 ^ k := by
  simp only [lowBudgetFinset, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨(le_D k r).trans_lt h, h⟩

theorem coe_lowBudgetFinset (k : ℕ) :
    (↑(lowBudgetFinset k) : Set ℕ) = lowBudgetWidths k := by
  ext r
  exact mem_lowBudgetFinset

theorem zero_mem_lowBudgetWidths {k : ℕ} (hk : 2 ≤ k) :
    0 ∈ lowBudgetWidths k := by
  have h : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  change D k 0 < 2 ^ k
  rw [D_zero]
  omega

/-- The exact polynomial expansion in the paper, valid also at width zero. -/
theorem D_cast_real (k r : ℕ) :
    (D k r : ℝ) =
      3 + (r : ℝ) * ((r : ℝ) - 1) +
        ((k : ℝ) * (r : ℝ)) * ((k : ℝ) * (r : ℝ) - 1) / 2 := by
  simp only [D, delta, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_choose_two]
  ring

/-- Removing the negative linear terms gives the readable quadratic budget. -/
theorem D_cast_real_le (k r : ℕ) :
    (D k r : ℝ) ≤ 3 + (r : ℝ) ^ 2 * (1 + (k : ℝ) ^ 2 / 2) := by
  rw [D_cast_real]
  have hkr : 0 ≤ (k : ℝ) * (r : ℝ) := by positivity
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

/-- The exact necessary inequality, conditional on the obstruction budget. -/
theorem exact_necessary_inequality {k r : ℕ} (h : 2 ^ k ≤ D k r) :
    (2 : ℝ) ^ k ≤
      3 + (r : ℝ) * ((r : ℝ) - 1) +
        ((k : ℝ) * (r : ℝ)) * ((k : ℝ) * (r : ℝ) - 1) / 2 := by
  rw [← D_cast_real]
  exact_mod_cast h

/-- The two inequalities displayed immediately before the paper's square-root bound. -/
theorem readable_inequality {k r : ℕ} (h : 2 ^ k ≤ D k r) :
    (2 : ℝ) ^ k - 3 ≤
      (r : ℝ) * ((r : ℝ) - 1) +
        ((k : ℝ) * (r : ℝ)) * ((k : ℝ) * (r : ℝ) - 1) / 2 ∧
    (r : ℝ) * ((r : ℝ) - 1) +
        ((k : ℝ) * (r : ℝ)) * ((k : ℝ) * (r : ℝ) - 1) / 2 ≤
      (r : ℝ) ^ 2 * (1 + (k : ℝ) ^ 2 / 2) := by
  have h₁ := exact_necessary_inequality h
  have h₂ := D_cast_real_le k r
  rw [D_cast_real] at h₂
  constructor <;> linarith

/-- The real-valued square-root lower bound, without any restriction on `k`. -/
theorem sqrt_lower_bound {k r : ℕ} (h : 2 ^ k ≤ D k r) :
    Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2)) ≤ (r : ℝ) := by
  apply (Real.sqrt_le_left (Nat.cast_nonneg r)).mpr
  have hden : 0 < 1 + (k : ℝ) ^ 2 / 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hb := readable_inequality h
  exact hb.1.trans hb.2

/-- The integer ceiling form of the paper's readable lower bound. -/
theorem ceil_sqrt_lower_bound {k r : ℕ} (h : 2 ^ k ≤ D k r) :
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉ ≤ (r : ℤ) := by
  apply Int.ceil_le.mpr
  exact_mod_cast sqrt_lower_bound h

/-- The same lower bound stated wholly as an inequality of natural numbers. -/
theorem natCeil_sqrt_lower_bound {k r : ℕ} (h : 2 ^ k ≤ D k r) :
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤ r := by
  exact Nat.ceil_le.mpr (sqrt_lower_bound h)

/-- The budget is monotone in its width parameter. -/
theorem D_mono_width (k : ℕ) : Monotone (D k) := by
  intro r s hrs
  have h₁ := Nat.choose_le_choose 2 hrs
  have h₂ := Nat.choose_le_choose 2 (Nat.mul_le_mul_left k hrs)
  unfold D delta
  omega

/-- A convenient elementary exponential-versus-quadratic estimate. -/
theorem sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- At an explicit arity depending on `B`, every width at most `B` is low-budget. -/
theorem budget_lt_two_pow_at_explicit_arity (B : ℕ) :
    D (4 * B + 8) B < 2 ^ (4 * B + 8) := by
  let n := 2 * B + 4
  have hn : 4 ≤ n := by omega
  have hpow : n ^ 4 ≤ 2 ^ (2 * n) := by
    calc
      n ^ 4 = (n ^ 2) ^ 2 := by ring
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (sq_le_two_pow hn) 2
      _ = 2 ^ (2 * n) := by rw [← pow_mul]; congr 1; omega
  have hpowR : (n : ℝ) ^ 4 ≤ (2 : ℝ) ^ (2 * n) := by exact_mod_cast hpow
  have hpoly :
      3 + (B : ℝ) ^ 2 * (1 + ((2 * n : ℕ) : ℝ) ^ 2 / 2) < (n : ℝ) ^ 4 := by
    dsimp [n]
    push_cast
    have hpos : 0 < 8 * (B : ℝ) ^ 4 + 96 * (B : ℝ) ^ 3 +
        351 * (B : ℝ) ^ 2 + 512 * (B : ℝ) + 253 := by positivity
    nlinarith only [hpos]
  have hbudgetR : (D (2 * n) B : ℝ) < (2 : ℝ) ^ (2 * n) :=
    lt_of_le_of_lt (D_cast_real_le (2 * n) B) (hpoly.trans_le hpowR)
  have hbudget : D (2 * n) B < 2 ^ (2 * n) := by exact_mod_cast hbudgetR
  convert hbudget using 1 <;> congr 1 <;> dsimp [n] <;> omega

/-- The budget condition alone forces unbounded widths as the arity varies.
This is an arithmetic implication, not an assertion that any particular family
of matchgate problems satisfies the condition. -/
theorem arbitrarily_large_required_width (B : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ r : ℕ, 2 ^ k ≤ D k r → B < r := by
  refine ⟨4 * B + 8, by omega, ?_⟩
  intro r hr
  by_contra h
  have hrB : r ≤ B := by omega
  have hbudget := (D_mono_width (4 * B + 8) hrB).trans_lt
    (budget_lt_two_pow_at_explicit_arity B)
  omega

/-- Any family meeting the obstruction budget at each arity has unbounded widths.
The budget hypotheses remain explicit. -/
theorem unbounded_widths_of_budget (width : ℕ → ℕ)
    (hbudget : ∀ k : ℕ, 2 ≤ k → 2 ^ k ≤ D k (width k)) :
    ∀ B : ℕ, ∃ k : ℕ, 2 ≤ k ∧ B < width k := by
  intro B
  obtain ⟨k, hk, h⟩ := arbitrarily_large_required_width B
  exact ⟨k, hk, h (width k) (hbudget k hk)⟩

end MatchgateWidth
