import MatchgateWidth.BinaryLiftMatrix
import MatchgateWidth.FullRowDecoder

/-!
# Source rank range and standard inclusions

The rank statement and inclusions in `paper/source/ITCS-arxiv.tex`, lines
1097–1125, in the literal increasing-input/decreasing-output convention.
The physical inclusion uses the final output ports, so its logical output
word is the input followed by zeroes.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

/-- A nonzero ordered matchgate has a unique rank exponent in the full arity range. -/
theorem OrderedMatchgateMatrix.existsUnique_rank_exponent {a b : ℕ}
    {P : Matrix (BooleanInput a) (BooleanInput b) ℂ}
    (hP : OrderedMatchgateMatrix P) (hne : P ≠ 0) :
    ∃! d : ℕ, d ≤ min a b ∧ P.rank = 2 ^ d := by
  have hr : P.rank ≠ 0 := by
    intro hz
    apply hne
    have hs : Submodule.span ℂ (Set.range P.row) = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rwa [← Matrix.rank_eq_finrank_span_row]
    ext i j
    have hi : P.row i ∈ Submodule.span ℂ (Set.range P.row) :=
      Submodule.subset_span ⟨i, rfl⟩
    rw [hs, Submodule.mem_bot] at hi
    exact congrFun hi j
  obtain ⟨d, hd⟩ := hP.rank_zero_or_power.resolve_left hr
  refine ⟨d, ⟨?_, hd⟩, ?_⟩
  · apply le_min
    · apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      simpa [hd, BooleanInput] using Matrix.rank_le_card_height P
    · apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      simpa [hd, BooleanInput] using Matrix.rank_le_card_width P
  · intro e he
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact he.2.symm.trans hd

/-- Append zeroes to the logical output word, without reversing its active bits. -/
def standardInclusionWord {r t : ℕ} (_h : r ≤ t) (x : BooleanInput r) :
    BooleanInput t :=
  fun i => if hi : i.val < r then x ⟨i.val, hi⟩ else 0

@[simp] theorem standardInclusionWord_castLE {r t : ℕ} (h : r ≤ t)
    (x : BooleanInput r) (i : Fin r) :
    standardInclusionWord h x (i.castLE h) = x i := by
  simp [standardInclusionWord]

@[simp] theorem standardInclusionWord_inactive {r t : ℕ} (h : r ≤ t)
    (x : BooleanInput r) (i : Fin t) (hi : r ≤ i.val) :
    standardInclusionWord h x i = 0 := by
  simp [standardInclusionWord, Nat.not_lt.mpr hi]

theorem standardInclusionWord_injective {r t : ℕ} (h : r ≤ t) :
    Function.Injective (standardInclusionWord h) := by
  intro x y hxy
  funext i
  simpa using congrFun hxy (i.castLE h)

/-- Physical active ports are the last `r` output ports; reversing to logical
coordinates puts the active bits first, as in the source's `(x,0^(t-r))`. -/
def standardInclusionPhysicalEmbedding {r t : ℕ} (h : r ≤ t) : Fin r ↪ Fin t where
  toFun i := (i.rev.castLE h).rev
  inj' := by
    intro i j hij
    have h' := congrArg Fin.rev hij
    simp only [Fin.rev_rev] at h'
    have h'' : i.rev = j.rev := Fin.ext (show i.rev.val = j.rev.val from congrArg (fun q : Fin t => q.val) h')
    simpa using congrArg Fin.rev h''

@[simp] theorem standardInclusionPhysicalEmbedding_apply {r t : ℕ} (h : r ≤ t)
    (i : Fin r) : standardInclusionPhysicalEmbedding h i = (i.rev.castLE h).rev := rfl

theorem standardInclusionPhysicalEmbedding_strictMono {r t : ℕ} (h : r ≤ t) :
    StrictMono (standardInclusionPhysicalEmbedding h) := by
  intro i j hij
  change (i.rev.castLE h).rev < (j.rev.castLE h).rev
  simp only [Fin.lt_def, Fin.val_rev, Fin.val_castLE] at hij ⊢
  have hi := i.isLt
  have hj := j.isLt
  omega

@[simp] theorem pinnedOutputWord_standardInclusion {r t : ℕ} (h : r ≤ t)
    (x : BooleanInput r) :
    pinnedOutputWord (standardInclusionPhysicalEmbedding h) ∅ x =
      standardInclusionWord h x := by
  apply (booleanSubsetEquiv t).injective
  ext i
  simp only [pinnedOutputWord, Equiv.apply_symm_apply,
    mem_reversePortSubset, Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true, and_true,
    false_and, or_false, Finset.mem_map, mem_booleanSubsetEquiv]
  by_cases hi : i.val < r
  · have he : standardInclusionPhysicalEmbedding h (⟨i.val, hi⟩ : Fin r).rev = i.rev := by
      apply Fin.ext
      simp only [standardInclusionPhysicalEmbedding_apply, Fin.rev_rev, Fin.val_rev,
        Fin.val_castLE]
    simp only [standardInclusionWord, dite_eq_left hi]
    constructor
    · rintro ⟨j, hj, hj'⟩
      have hj'' := (standardInclusionPhysicalEmbedding h).injective (hj'.trans he.symm)
      simpa [hj''] using hj
    · intro hx
      exact ⟨(⟨i.val, hi⟩ : Fin r).rev, by simpa using hx, he⟩
  · simp only [standardInclusionWord, dite_eq_right hi]
    simp only [Fin.zero_ne_one, iff_false, not_exists, not_and]
    intro j _ hj
    have hv := congrArg Fin.val (congrArg Fin.rev hj)
    simp only [standardInclusionPhysicalEmbedding_apply,
      Fin.rev_rev, Fin.val_castLE] at hv
    have hjlt := j.rev.isLt
    omega

variable {R : Type*} [CommRing R]

/-- The source's literal `J_(r,t)`, with input rows and output columns. -/
def standardInclusion {r t : ℕ} (h : r ≤ t) :
    Matrix (BooleanInput r) (BooleanInput t) R :=
  (pinnedOutputInclusion (standardInclusionPhysicalEmbedding h) ∅).transpose

@[simp] theorem standardInclusion_apply {r t : ℕ} (h : r ≤ t)
    (x : BooleanInput r) (y : BooleanInput t) :
    standardInclusion (R := R) h x y =
      if y = standardInclusionWord h x then 1 else 0 := by
  simp [standardInclusion, Matrix.transpose_apply]

theorem standardInclusion_orderedMatchgate {r t : ℕ} (h : r ≤ t) :
    OrderedMatchgateMatrix (standardInclusion (R := R) h) :=
  (pinnedOutputInclusion_orderedMatchgate _
    (standardInclusionPhysicalEmbedding_strictMono h) ∅).transpose

/-- The literal standard inclusion satisfies `J_(r,t) J_(r,t)^T = I_(2^r)`. -/
@[simp] theorem standardInclusion_mul_transpose {r t : ℕ} (h : r ≤ t) :
    standardInclusion (R := R) h * (standardInclusion (R := R) h).transpose = 1 := by
  classical
  ext x z
  simp only [Matrix.mul_apply, standardInclusion_apply, Matrix.transpose_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, Matrix.one_apply]
  simp only [(standardInclusionWord_injective h).eq_iff]

/-- With output arity written as `r + s`, the logical word is literally
`(x, 0^s)`. -/
@[simp] theorem standardInclusionWord_add (r s : ℕ) (x : BooleanInput r) :
    standardInclusionWord (Nat.le_add_right r s) x = Fin.append x (fun _ => 0) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [standardInclusionWord]
  | right i => simp [standardInclusionWord, Nat.not_lt.mpr (Nat.le_add_right _ _)]

/-- The physical active port `i` is exactly `t-r+i`; the initial `t-r`
physical output ports are the inactive ones. -/
theorem standardInclusionPhysicalEmbedding_val {r t : ℕ} (h : r ≤ t) (i : Fin r) :
    (standardInclusionPhysicalEmbedding h i).val = t - r + i.val := by
  simp only [standardInclusionPhysicalEmbedding_apply, Fin.val_rev, Fin.val_castLE]
  have hi := i.isLt
  omega

section Field
variable {K : Type*} [Field K]

@[simp] theorem standardInclusion_rank {r t : ℕ} (h : r ≤ t) :
    (standardInclusion (R := K) h).rank = 2 ^ r := by
  apply le_antisymm
  · simpa [BooleanInput] using Matrix.rank_le_card_height (standardInclusion (R := K) h)
  · have hr := Matrix.rank_mul_le_left (standardInclusion (R := K) h)
      (standardInclusion (R := K) h).transpose
    simpa [BooleanInput] using hr

/-- Canonical ordered matchgate with `d` active input-output wires and all
remaining modes pinned to zero, constructed using the literal inclusions. -/
def canonicalPinnedMatchgate {a b d : ℕ} (ha : d ≤ a) (hb : d ≤ b) :
    Matrix (BooleanInput a) (BooleanInput b) K :=
  (standardInclusion ha).transpose * standardInclusion hb

theorem canonicalPinnedMatchgate_orderedMatchgate {a b d : ℕ}
    (ha : d ≤ a) (hb : d ≤ b) :
    OrderedMatchgateMatrix (canonicalPinnedMatchgate (K := K) ha hb) :=
  (standardInclusion_orderedMatchgate ha).transpose.mul
    (standardInclusion_orderedMatchgate hb)

/-- Recover the identity on active wires by restricting the inactive modes. -/
@[simp] theorem canonicalPinnedMatchgate_recover {a b d : ℕ}
    (ha : d ≤ a) (hb : d ≤ b) :
    standardInclusion (R := K) ha * canonicalPinnedMatchgate (K := K) ha hb *
      (standardInclusion (R := K) hb).transpose =
        (1 : Matrix (BooleanInput d) (BooleanInput d) K) := by
  simp only [canonicalPinnedMatchgate, ← Matrix.mul_assoc,
    standardInclusion_mul_transpose, Matrix.one_mul]

@[simp] theorem canonicalPinnedMatchgate_rank {a b d : ℕ}
    (ha : d ≤ a) (hb : d ≤ b) :
    (canonicalPinnedMatchgate (K := K) ha hb).rank = 2 ^ d := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_right (standardInclusion (R := K) ha).transpose
      (standardInclusion (R := K) hb)).trans_eq (standardInclusion_rank hb)
  · have hr := (Matrix.rank_mul_le_left
      (standardInclusion ha * canonicalPinnedMatchgate (K := K) ha hb)
      (standardInclusion (R := K) hb).transpose).trans
        (Matrix.rank_mul_le_right (standardInclusion ha)
          (canonicalPinnedMatchgate (K := K) ha hb))
    simpa [BooleanInput] using hr

theorem canonicalPinnedMatchgate_ne_zero {a b d : ℕ}
    (ha : d ≤ a) (hb : d ≤ b) :
    canonicalPinnedMatchgate (K := K) ha hb ≠ 0 := by
  intro hz
  have hr := canonicalPinnedMatchgate_rank (K := K) ha hb
  rw [hz, Matrix.rank_zero] at hr
  exact (Nat.ne_of_gt (by positivity : 0 < 2 ^ d)) hr.symm

/-- Conversely, every exponent from `0` through `min(a,b)` occurs for a
nonzero exact ordered matchgate with these fixed arities. -/
theorem exists_orderedMatchgate_rank_of_le_min (a b d : ℕ) (hd : d ≤ min a b) :
    ∃ P : Matrix (BooleanInput a) (BooleanInput b) K,
      OrderedMatchgateMatrix P ∧ P ≠ 0 ∧ P.rank = 2 ^ d := by
  have ha := hd.trans (min_le_left a b)
  have hb := hd.trans (min_le_right a b)
  exact ⟨canonicalPinnedMatchgate ha hb, canonicalPinnedMatchgate_orderedMatchgate ha hb,
    canonicalPinnedMatchgate_ne_zero ha hb, canonicalPinnedMatchgate_rank ha hb⟩

/-- With unrestricted input and output arities, every nonnegative rank
exponent occurs. -/
theorem exists_orderedMatchgate_rank_exponent (d : ℕ) :
    ∃ a b : ℕ, ∃ P : Matrix (BooleanInput a) (BooleanInput b) K,
      OrderedMatchgateMatrix P ∧ P ≠ 0 ∧ P.rank = 2 ^ d := by
  exact ⟨d, d, exists_orderedMatchgate_rank_of_le_min d d d (by simp)⟩

end Field
end
end MatchgateWidth
