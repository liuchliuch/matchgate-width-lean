import MatchgateWidth.BlockInterpolation

/-!
# Logical-block order for the interpolation matrix

Consecutive incidence pairs are regrouped by logical port with positive Pfaffian
sign. This file connects the component-major construction to repetition blocks.
-/

namespace MatchgateWidth

noncomputable section

/-- All incidence pairs, ordered first by subset and then increasingly within it. -/
def allIncidencePairs (k : ℕ) : List (PairIncidence k) :=
  (nonemptySubsets (Finset.univ : Finset (Fin k))).toList.flatMap
    fun S => (List.finRange S.card).map (fun j => (⟨S, j⟩ : PairIncidence k))

/-- Preserve `a,b` order inside every incidence pair. -/
def expandIncidencePairs {k : ℕ} (ps : List (PairIncidence k)) : List (InterpolationMode k) :=
  ps.flatMap fun p => [(p, false), (p, true)]

/-- Each logical block is in the same fixed subset order. -/
def logicalIncidenceBlock {k : ℕ} (i : Fin k) : List (PairIncidence k) :=
  (allIncidencePairs k).filter fun p => decide (incidencePort p = i)

/-- Selection in increasing logical-block order, retaining entire pair chunks. -/
def blockMajorPairs {k : ℕ} (T : Finset (Fin k)) : List (PairIncidence k) :=
  ((List.finRange k).filter fun i => decide (i ∈ T)).flatMap logicalIncidenceBlock

/-- The actual mode list selected by Boolean repetition on logical blocks. -/
def blockMajorModes {k : ℕ} (T : Finset (Fin k)) : List (InterpolationMode k) :=
  expandIncidencePairs (blockMajorPairs T)

/-- Filtering the complete incidence enumeration is the component-major mask. -/
theorem componentMajorModes_eq {k : ℕ} (T : Finset (Fin k)) :
    componentMajorModes T = expandIncidencePairs
      ((allIncidencePairs k).filter fun p => decide (incidencePort p ∈ T)) := by
  simp [componentMajorModes, expandIncidencePairs, allIncidencePairs,
    List.filter_flatMap, List.filter_map, List.flatMap_assoc, List.flatMap_map,
    componentModes, incidencePort, Function.comp_def]
  rfl

/-- Every incidence appears only once. -/
theorem allIncidencePairs_nodup (k : ℕ) : (allIncidencePairs k).Nodup := by
  rw [allIncidencePairs, List.nodup_flatMap]
  constructor
  · intro S _
    exact (List.nodup_finRange S.card).map (fun a b h => by simpa using h)
  · apply List.Pairwise.imp _ (Finset.nodup_toList _)
    intro S U hSU
    apply List.disjoint_left.mpr
    intro p hp hq
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hp
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hq
    exact hSU (congrArg Sigma.fst (hj.trans hl.symm))

theorem blockMajorPairs_nodup {k : ℕ} (T : Finset (Fin k)) :
    (blockMajorPairs T).Nodup := by
  rw [blockMajorPairs, List.nodup_flatMap]
  constructor
  · intro i _
    exact (allIncidencePairs_nodup k).filter _
  · apply List.Pairwise.imp _ ((List.nodup_finRange k).filter _)
    intro i j hij
    apply List.disjoint_left.mpr
    intro p hp hq
    have hi : incidencePort p = i := by simpa [logicalIncidenceBlock] using (List.mem_filter.mp hp).2
    have hj : incidencePort p = j := by simpa [logicalIncidenceBlock] using (List.mem_filter.mp hq).2
    exact hij (hi.symm.trans hj)

theorem mem_blockMajorPairs {k : ℕ} (T : Finset (Fin k)) (p : PairIncidence k) :
    p ∈ blockMajorPairs T ↔ p ∈ allIncidencePairs k ∧ incidencePort p ∈ T := by
  simp only [blockMajorPairs, List.mem_flatMap, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq, logicalIncidenceBlock]
  constructor
  · rintro ⟨i, hi, hp, heq⟩
    exact ⟨hp, heq ▸ hi⟩
  · rintro ⟨hp, hi⟩
    exact ⟨incidencePort p, hi, hp, rfl⟩

/-- The regrouping is a genuine permutation of complete incidence pairs. -/
theorem blockMajorPairs_perm {k : ℕ} (T : Finset (Fin k)) :
    (blockMajorPairs T).Perm
      ((allIncidencePairs k).filter fun p => decide (incidencePort p ∈ T)) := by
  apply (List.perm_ext_iff_of_nodup (blockMajorPairs_nodup T)
    ((allIncidencePairs_nodup k).filter _)).mpr
  intro p
  simp [mem_blockMajorPairs]

/-- Regrouping the explicitly constructed matrix has sign `+1`. -/
theorem interpolationMatrix_blockMajor_pfaffian {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (T : Finset (Fin k)) :
    pfaffianList (interpolationMatrix y) (blockMajorModes T) =
      ∏ S ∈ nonemptySubsets T, y S := by
  rw [← interpolationMatrix_componentMajor_pfaffian y T, componentMajorModes_eq]
  have h := pfaffianList_pairChunks_perm (interpolationMatrix y)
    (interpolationMatrix_skew y)
    ((blockMajorPairs_perm T).map (fun p => ((p, false), (p, true)))) [] []
  simpa [blockMajorModes, expandIncidencePairs, List.flatMap_map] using h

/-- The normalized nowhere-zero table is the actual block-selected Pfaffian. -/
theorem tableInterpolationMatrix_blockMajor {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) (T : Finset (Fin k)) :
    pfaffianList (tableInterpolationMatrix f hf) (blockMajorModes T) = f T / f ∅ := by
  exact (interpolationMatrix_blockMajor_pfaffian _ T).trans
    (prod_nonzeroMultiplicativeMobius f hf T)

/-- The component enumeration contains every finite incidence. -/
theorem mem_allIncidencePairs {k : ℕ} (p : PairIncidence k) :
    p ∈ allIncidencePairs k := by
  rcases p with ⟨S, j⟩
  apply List.mem_flatMap.mpr
  refine ⟨S, ?_, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩
  apply Finset.mem_toList.mpr
  apply mem_nonemptySubsets.mpr
  exact ⟨Finset.ne_empty_of_mem ((S.orderEmbOfFin_mem rfl j)), Finset.subset_univ S⟩

/-- Two incidences in one logical block have distinct subset labels. -/
theorem logicalIncidenceBlock_subset_injective {k : ℕ} (i : Fin k) :
    ∀ p ∈ logicalIncidenceBlock i, ∀ q ∈ logicalIncidenceBlock i,
      p.1 = q.1 → p = q := by
  rintro ⟨S, j⟩ hp ⟨U, l⟩ hq h
  change S = U at h
  subst U
  have hp' : S.orderEmbOfFin rfl j = i := by
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have hq' : S.orderEmbOfFin rfl l = i := by
    exact of_decide_eq_true (List.mem_filter.mp hq).2
  exact congrArg (Sigma.mk S) ((S.orderEmbOfFin rfl).injective (hp'.trans hq'.symm))

/-- Subset labels of one logical block are exactly the subsets containing its port. -/
theorem logicalIncidenceBlock_subsets {k : ℕ} (i : Fin k) :
    ((logicalIncidenceBlock i).map Sigma.fst).toFinset =
      (Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S) := by
  ext S
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨U, j⟩, hp, h⟩
    have hp' : U.orderEmbOfFin rfl j = i := by
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    simp [← h, ← hp']
  · intro hi
    let j := (S.orderIsoOfFin rfl).symm ⟨i, hi⟩
    refine ⟨⟨S, j⟩, ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨mem_allIncidencePairs _, ?_⟩
    apply decide_eq_true
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)

/-- Exactly half the subsets contain a specified port. -/
theorem card_subsets_containing {k : ℕ} (i : Fin k) :
    ((Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S)).card =
      2 ^ (k - 1) := by
  let U : Finset (Fin k) := Finset.univ.erase i
  have heq : (Finset.univ.filter (fun S : Finset (Fin k) => i ∈ S)) =
      U.powerset.image (insert i) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · intro hi
      exact ⟨S.erase i, Finset.erase_subset_erase i (Finset.subset_univ S),
        Finset.insert_erase hi⟩
    · rintro ⟨V, _, rfl⟩
      exact Finset.mem_insert_self i V
  rw [heq, Finset.card_image_iff.mpr, Finset.card_powerset]
  · simp [U]
  · intro S hS T hT h
    have hiS : i ∉ S := fun hmem => by
      have := (Finset.mem_powerset.mp hS) hmem
      exact (Finset.mem_erase.mp this).1 rfl
    have hiT : i ∉ T := fun hmem => by
      have := (Finset.mem_powerset.mp hT) hmem
      exact (Finset.mem_erase.mp this).1 rfl
    have he := congrArg (fun V : Finset (Fin k) => V.erase i) h
    simpa [hiS, hiT] using he

/-- One incidence pair for each of the `2^(k-1)` subsets containing the port. -/
theorem logicalIncidenceBlock_length {k : ℕ} (i : Fin k) :
    (logicalIncidenceBlock i).length = 2 ^ (k - 1) := by
  have hd : ((logicalIncidenceBlock i).map Sigma.fst).Nodup :=
    (allIncidencePairs_nodup k).filter _ |>.map_on
      (logicalIncidenceBlock_subset_injective i)
  have hc := List.toFinset_card_of_nodup hd
  rw [logicalIncidenceBlock_subsets, List.length_map] at hc
  exact hc.symm.trans (card_subsets_containing i)

/-- An actual logical repetition block of modes. -/
def logicalModeBlock {k : ℕ} (i : Fin k) : List (InterpolationMode k) :=
  expandIncidencePairs (logicalIncidenceBlock i)

theorem expandIncidencePairs_length {k : ℕ} (ps : List (PairIncidence k)) :
    (expandIncidencePairs ps).length = 2 * ps.length := by
  induction ps with
  | nil => simp [expandIncidencePairs]
  | cons p ps ih =>
    simp [expandIncidencePairs] at ih ⊢
    omega

/-- Each logical block has exactly `t = 2^k` modes. -/
theorem logicalModeBlock_length {k : ℕ} (i : Fin k) :
    (logicalModeBlock i).length = 2 ^ k := by
  rw [logicalModeBlock, expandIncidencePairs_length, logicalIncidenceBlock_length]
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have he : k = (k - 1) + 1 := by omega
  conv_rhs => rw [he, pow_succ]
  omega

/-- Selecting Boolean ones concatenates precisely their entire repetition blocks. -/
theorem blockMajorModes_eq_logicalBlocks {k : ℕ} (T : Finset (Fin k)) :
    blockMajorModes T =
      ((List.finRange k).filter fun i => decide (i ∈ T)).flatMap logicalModeBlock := by
  simp only [blockMajorModes, blockMajorPairs,
    expandIncidencePairs, List.flatMap_assoc]
  rfl

/-- Pair expansion introduces no repetitions. -/
theorem expandIncidencePairs_nodup {k : ℕ} {ps : List (PairIncidence k)}
    (h : ps.Nodup) : (expandIncidencePairs ps).Nodup := by
  rw [expandIncidencePairs, List.nodup_flatMap]
  constructor
  · intro p _
    simp
  · apply List.Pairwise.imp _ h
    intro p q hpq
    apply List.disjoint_left.mpr
    intro m hm hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hn
    rcases hm with rfl | rfl <;> rcases hn with h | h
    all_goals exact hpq (congrArg Prod.fst h)

/-- The complete logical-block order enumerates each mode exactly once. -/
theorem fullBlockMajorModes_nodup (k : ℕ) :
    (blockMajorModes (Finset.univ : Finset (Fin k))).Nodup :=
  expandIncidencePairs_nodup (blockMajorPairs_nodup _)

theorem mem_fullBlockMajorModes {k : ℕ} (m : InterpolationMode k) :
    m ∈ blockMajorModes (Finset.univ : Finset (Fin k)) := by
  rcases m with ⟨p, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨p, (mem_blockMajorPairs _ _).mpr ⟨mem_allIncidencePairs p, Finset.mem_univ _⟩, ?_⟩
  cases b <;> simp

/-- Every mode in a logical block has that block's logical label. -/
theorem logicalModeBlock_port {k : ℕ} (i : Fin k) (m : InterpolationMode k)
    (hm : m ∈ logicalModeBlock i) : incidencePort m.1 = i := by
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hm
  have hp' : incidencePort p = i := of_decide_eq_true (List.mem_filter.mp hp).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact hp'

/-- Boolean repetition of each input bit into a consecutive `2^k`-mode block. -/
def booleanRepetitionWord {k : ℕ} (x : Fin k → Bool) : List Bool :=
  (List.finRange k).flatMap fun i => List.replicate (2 ^ k) (x i)

/-- The finite mode order realizes exactly the Boolean repetition word. -/
theorem blockMajorModes_repetitionWord {k : ℕ} (x : Fin k → Bool) :
    (blockMajorModes (Finset.univ : Finset (Fin k))).map
      (fun m => x (incidencePort m.1)) = booleanRepetitionWord x := by
  rw [blockMajorModes_eq_logicalBlocks]
  simp only [Finset.mem_univ, decide_true, List.filter_true, List.map_flatMap,
    booleanRepetitionWord]
  apply List.flatMap_congr
  intro i _
  rw [← logicalModeBlock_length i]
  apply List.map_eq_replicate_iff.mpr
  intro m hm
  rw [logicalModeBlock_port i m hm]

/-- Filtering a block-constant predicate is the same as selecting complete blocks. -/
private theorem filter_flatMap_constant {α β : Type*} (ls : List α)
    (blocks : α → List β) (p : β → Bool) (q : α → Bool)
    (h : ∀ a ∈ ls, ∀ b ∈ blocks a, p b = q a) :
    (ls.flatMap blocks).filter p = (ls.filter q).flatMap blocks := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    simp only [List.flatMap_cons, List.filter_append]
    rw [ih (fun z hz => h z (by simp [hz]))]
    cases he : q a
    · have hn : (blocks a).filter p = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        rw [h a (by simp) b hb, he]
        simp
      simp [he, hn]
    · have hy : (blocks a).filter p = blocks a := by
        apply List.filter_eq_self.mpr
        intro b hb
        rw [h a (by simp) b hb, he]
      simp [he, hy]

/-- Selecting the one bits of the repetition word gives exactly the desired
ordered principal submatrix, with no ordering or component-product assumption. -/
theorem blockMajorModes_booleanSelection {k : ℕ} (x : Fin k → Bool) :
    (blockMajorModes (Finset.univ : Finset (Fin k))).filter
      (fun m => x (incidencePort m.1)) =
      blockMajorModes (Finset.univ.filter fun i => x i) := by
  simp only [blockMajorModes_eq_logicalBlocks, Finset.mem_univ, decide_true,
    List.filter_true, Finset.mem_filter, true_and, Bool.decide_eq_true]
  apply filter_flatMap_constant
  intro i _ m hm
  rw [logicalModeBlock_port i m hm]

/-- Any fixed ordering of the selected incidence pairs gives the same value.
Thus replacing the subset enumeration by the paper's lexicographic one introduces
no sign: every move permutes whole two-mode chunks. -/
theorem tableInterpolationMatrix_any_pairOrder {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) (T : Finset (Fin k))
    (ps : List (PairIncidence k)) (hdup : ps.Nodup)
    (hmem : ∀ p, p ∈ ps ↔ incidencePort p ∈ T) :
    pfaffianList (tableInterpolationMatrix f hf) (expandIncidencePairs ps) =
      f T / f ∅ := by
  have hp : ps.Perm (blockMajorPairs T) := by
    apply (List.perm_ext_iff_of_nodup hdup (blockMajorPairs_nodup T)).mpr
    intro p
    simp only [hmem, mem_blockMajorPairs, mem_allIncidencePairs, true_and]
  have heq := pfaffianList_pairChunks_perm (tableInterpolationMatrix f hf)
    (interpolationMatrix_skew _) (hp.map (fun p => ((p, false), (p, true)))) [] []
  have heq' : pfaffianList (tableInterpolationMatrix f hf) (expandIncidencePairs ps) =
      pfaffianList (tableInterpolationMatrix f hf) (blockMajorModes T) := by
    simpa [expandIncidencePairs, blockMajorModes, List.flatMap_map] using heq
  exact heq'.trans (tableInterpolationMatrix_blockMajor f hf T)


/-- Full algebraic conclusion: an actual finite skew matrix, exact width `2^k`,
a genuine exhaustive mode order, and every Boolean repetition Pfaffian.
This theorem makes no assertion of planar realization. -/
theorem exists_algebraic_boolean_repetition_interpolation
    (k : ℕ) {K : Type*} [Field K] (f : Finset (Fin k) → K)
    (hf : ∀ T, f T ≠ 0) :
    ∃ A : Matrix (InterpolationMode k) (InterpolationMode k) K,
      (∀ m n, A m n = -A n m) ∧ (∀ m, A m m = 0) ∧
      (∀ i : Fin k, (logicalModeBlock i).length = 2 ^ k) ∧
      (blockMajorModes (Finset.univ : Finset (Fin k))).Nodup ∧
      (∀ m, m ∈ blockMajorModes (Finset.univ : Finset (Fin k))) ∧
      ∀ x : Fin k → Bool,
        pfaffianList A ((blockMajorModes (Finset.univ : Finset (Fin k))).filter
          (fun m => x (incidencePort m.1))) =
            f (Finset.univ.filter fun i => x i) / f ∅ := by
  refine ⟨tableInterpolationMatrix f hf, interpolationMatrix_skew _,
    interpolationMatrix_diag _, logicalModeBlock_length, fullBlockMajorModes_nodup k,
    mem_fullBlockMajorModes, ?_⟩
  intro x
  rw [blockMajorModes_booleanSelection]
  exact tableInterpolationMatrix_blockMajor f hf _

end
end MatchgateWidth
