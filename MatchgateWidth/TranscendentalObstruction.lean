import MatchgateWidth.IndependentPrimeExponentials
import MatchgateWidth.ExactMatchgateBounds
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Nth

/-! # Proposition 6.2: the exact lexicographic prime-exponential obstruction

The table uses the first `2^k` primes in the paper's stated lexicographic order.
No algebraic independence or rank premise is left to the caller.
-/
namespace MatchgateWidth
noncomputable section
open scoped BigOperators

/-- Zero-based lexicographic index, with the first port the most significant bit. -/
def booleanLexIndex : {k : ℕ} → BooleanInput k → ℕ
  | 0, _ => 0
  | k + 1, z => (z 0).val * 2 ^ k + booleanLexIndex (fun i => z i.succ)

/-- The exact sum in the source's one-based index, minus one. -/
theorem booleanLexIndex_eq_sum {k : ℕ} (z : BooleanInput k) :
    booleanLexIndex z = ∑ i : Fin k, (z i).val * 2 ^ (k - 1 - i.val) := by
  induction k with
  | zero => simp [booleanLexIndex]
  | succ k ih =>
    rw [booleanLexIndex, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega

theorem booleanLexIndex_lt {k : ℕ} (z : BooleanInput k) : booleanLexIndex z < 2 ^ k := by
  induction k with
  | zero => simp [booleanLexIndex]
  | succ k ih =>
    have ht := ih (fun i => z i.succ)
    have hz := (z 0).isLt
    simp only [booleanLexIndex, pow_succ]
    have hpos : 0 < 2 ^ k := by positivity
    interval_cases h : (z 0).val <;> simp only [ zero_mul, one_mul] <;> omega

theorem booleanLexIndex_injective (k : ℕ) :
    Function.Injective (booleanLexIndex (k := k)) := by
  induction k with
  | zero => intro z w h; exact Subsingleton.elim _ _
  | succ k ih =>
    intro z w h
    have hz := booleanLexIndex_lt (fun i => z i.succ)
    have hw := booleanLexIndex_lt (fun i => w i.succ)
    have h0 : z 0 = w 0 := by
      apply Fin.ext
      have ha := (z 0).isLt
      have hb := (w 0).isLt
      dsimp only [booleanLexIndex] at h
      interval_cases a : (z 0).val <;> interval_cases b : (w 0).val <;>
        simp only [  zero_mul, one_mul] at h ⊢ <;> omega
    have ht : (fun i : Fin k => z i.succ) = (fun i : Fin k => w i.succ) := by
      apply ih
      simpa only [booleanLexIndex, h0, Nat.add_left_cancel_iff] using h
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i => exact congrFun ht i

/-- The prime whose one-based index is `1 + booleanLexIndex z`. -/
def lexicographicPrime {k : ℕ} (z : BooleanInput k) : ℕ :=
  Nat.nth Nat.Prime (booleanLexIndex z)

theorem lexicographicPrime_prime {k : ℕ} (z : BooleanInput k) :
    (lexicographicPrime z).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _

theorem lexicographicPrime_injective (k : ℕ) :
    Function.Injective (lexicographicPrime (k := k)) :=
  (Nat.nth_injective Nat.infinite_setOfPred_prime).comp (booleanLexIndex_injective k)

/-- The source's literal closed-form real table `exp(sqrt(p_ind(z)))`. -/
def transcendentalTableReal (k : ℕ) : BooleanTable k ℝ :=
  fun z => Real.exp (Real.sqrt (lexicographicPrime z : ℝ))

/-- Its canonical inclusion in the complex signature field. -/
def transcendentalTable (k : ℕ) : BooleanTable k ℂ :=
  fun z => (transcendentalTableReal k z : ℂ)

theorem transcendentalTableReal_pos (k : ℕ) (z : BooleanInput k) :
    0 < transcendentalTableReal k z := Real.exp_pos _

theorem transcendentalTable_ne_zero (k : ℕ) (z : BooleanInput k) :
    transcendentalTable k z ≠ 0 := by
  change (transcendentalTableReal k z : ℂ) ≠ 0
  exact_mod_cast (ne_of_gt (transcendentalTableReal_pos k z))

theorem transcendentalTable_algebraicIndependent (k : ℕ) :
    AlgebraicIndependent ℚ (transcendentalTable k) := by
  unfold transcendentalTable transcendentalTableReal
  simp_rw [Complex.ofReal_exp]
  simpa only [primeSquareRoot] using algebraicIndependent_primeExponentials
      (lexicographicPrime (k := k)) lexicographicPrime_prime (lexicographicPrime_injective k)

/-- The actual value-generated field has the full `2^k` transcendence degree. -/
theorem transcendentalTable_trdeg (k : ℕ) :
    Algebra.trdeg ℚ (coordinateField (transcendentalTable k)) = (2 ^ k : ℕ) := by
  let f := transcendentalTable k
  let g : BooleanInput k → coordinateField f := fun z =>
    ⟨f z, IntermediateField.subset_adjoin _ _ (Set.mem_range_self z)⟩
  have hg : AlgebraicIndependent ℚ g :=
    (transcendentalTable_algebraicIndependent k).of_comp (coordinateField f).val
  apply le_antisymm
  · simpa [Fintype.card_fun, BooleanInput] using trdeg_adjoin_range_le_card f
  · simpa [Cardinal.mk_fintype, Fintype.card_fun, BooleanInput] using hg.cardinalMk_le_trdeg

/-- Every complete one-versus-rest flattening has rank exactly two. -/
theorem transcendentalTable_all_flattenings_rank_two (k : ℕ) (hk : 2 ≤ k) :
    ∀ i : Fin k, (oneVsRestFlattening (transcendentalTable k) i).rank = 2 :=
  algebraicIndependent_table_all_flattenings_rank_two hk _
    (transcendentalTable_algebraicIndependent k)

/-- The obstruction also applies directly to the literal identity locus. -/
theorem transcendentalTable_MGI_budget (k r : ℕ)
    (h : HasMGIStarRepresentation k r (transcendentalTable k)) : 2 ^ k ≤ D k r := by
  obtain ⟨g,Q,hg,hQ,hrep⟩ := h
  have heq : transcendentalTable k = sampledAlphabetStar Q g := funext hrep
  have ht := trdeg_sampledBooleanStar_coordinateField_le hQ hg
  rw [← heq, transcendentalTable_trdeg] at ht
  exact_mod_cast ht

/-- Proposition 6.2, with arbitrary complex-weight exact graph competitors and
all nonnegative widths, including width zero. -/
theorem transcendental_obstruction_proposition (k : ℕ) (hk : 2 ≤ k) :
    (∀ i : Fin k, (oneVsRestFlattening (transcendentalTable k) i).rank = 2) ∧
    (∀ (r : ℕ) (g : Fin 2 → BooleanTable r ℂ) (Q : BooleanTable (k*r) ℂ),
      (∀ b, ExactMatchgate (g b)) → ExactMatchgate Q →
      (∀ z, transcendentalTable k z =
        starContract (fun x => Q (flattenBooleanBlocks x)) (fun i => g (z i))) →
      2^k ≤ 2*delta r + delta (k*r)) := by
  refine ⟨transcendentalTable_all_flattenings_rank_two k hk, ?_⟩
  intro r g Q hg hQ hrep
  exact transcendentalTable_MGI_budget k r
    ⟨g,Q,(fun b => (hg b).matchgateIdentities),hQ.matchgateIdentities,hrep⟩

end
end MatchgateWidth
