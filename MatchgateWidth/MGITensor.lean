import MatchgateWidth.MatchgateIdentities

/-!
# Tensor products in consecutive boundary order

The tensor coordinate restricts a subset to its first and second consecutive
blocks. Its literal sorted-symmetric-difference identity is the sum of the two
factor identities, with the second shifted by the first difference's length.
-/
namespace MatchgateWidth
open scoped symmDiff

/-- Restrict a boundary subset to its first consecutive block. -/
def firstBlock {m n : ℕ} (S : Finset (Fin (m + n))) : Finset (Fin m) :=
  Finset.univ.filter fun i => Fin.castAdd n i ∈ S

/-- Restrict a boundary subset to its second consecutive block. -/
def secondBlock {m n : ℕ} (S : Finset (Fin (m + n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => Fin.natAdd m i ∈ S

@[simp] theorem mem_firstBlock {m n : ℕ} (S : Finset (Fin (m + n))) (i : Fin m) :
    i ∈ firstBlock S ↔ Fin.castAdd n i ∈ S := by simp [firstBlock]
@[simp] theorem mem_secondBlock {m n : ℕ} (S : Finset (Fin (m + n))) (i : Fin n) :
    i ∈ secondBlock S ↔ Fin.natAdd m i ∈ S := by simp [secondBlock]

private theorem block_ne {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

@[simp] theorem firstBlock_symmDiff {m n : ℕ} (A B : Finset (Fin (m + n))) :
    firstBlock (A ∆ B) = firstBlock A ∆ firstBlock B := by
  ext i
  simp [Finset.mem_symmDiff]
@[simp] theorem secondBlock_symmDiff {m n : ℕ} (A B : Finset (Fin (m + n))) :
    secondBlock (A ∆ B) = secondBlock A ∆ secondBlock B := by
  ext i
  simp [Finset.mem_symmDiff]

@[simp] theorem firstBlock_singleton_left {m n : ℕ} (i : Fin m) :
    firstBlock {Fin.castAdd n i} = {i} := by ext j; simp
@[simp] theorem secondBlock_singleton_left {m n : ℕ} (i : Fin m) :
    secondBlock {Fin.castAdd n i} = ∅ := by
  ext j
  simp [Ne.symm (block_ne i j)]
@[simp] theorem firstBlock_singleton_right {m n : ℕ} (i : Fin n) :
    firstBlock {Fin.natAdd m i} = ∅ := by
  ext j
  simp [block_ne j i]
@[simp] theorem secondBlock_singleton_right {m n : ℕ} (i : Fin n) :
    secondBlock {Fin.natAdd m i} = {i} := by ext j; simp

/-- Ordinary tensor product with the first boundary block preceding the second. -/
def consecutiveTensor {m n : ℕ} {R : Type*} [Mul R]
    (G : SubsetSignature m R) (H : SubsetSignature n R) :
    SubsetSignature (m + n) R := fun S => G (firstBlock S) * H (secondBlock S)

/-- Sorting a subset of consecutive blocks gives concatenated sorted restrictions. -/
theorem sort_blocks {m n : ℕ} (S : Finset (Fin (m + n))) :
    S.sort (· ≤ ·) =
      ((firstBlock S).sort (· ≤ ·)).map (Fin.castAdd n) ++
      ((secondBlock S).sort (· ≤ ·)).map (Fin.natAdd m) := by
  let xs := ((firstBlock S).sort (· ≤ ·)).map (Fin.castAdd n)
  let ys := ((secondBlock S).sort (· ≤ ·)).map (Fin.natAdd m)
  have hsorted : (xs ++ ys).SortedLT := by
    apply List.Pairwise.sortedLT
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [xs]
      rw [List.pairwise_map]
      change List.Pairwise (fun a b : Fin m => a < b) _
      exact (Finset.sortedLT_sort (firstBlock S)).pairwise
    · dsimp [ys]
      rw [List.pairwise_map]
      simpa only [Fin.natAdd_lt_natAdd_iff] using (Finset.sortedLT_sort (secondBlock S)).pairwise
    · intro a ha b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
      change i.val < m + j.val
      omega
  have hset : (xs ++ ys).toFinset = S := by
    ext i
    induction i using Fin.addCases with
    | left i =>
      simp only [List.mem_toFinset, List.mem_append, xs, ys, List.mem_map,
        Finset.mem_sort, mem_firstBlock, mem_secondBlock]
      constructor
      · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
        · simpa only [he] using hj
        · exact (block_ne i j he.symm).elim
      · intro hi
        exact Or.inl ⟨i, hi, rfl⟩
    | right i =>
      simp only [List.mem_toFinset, List.mem_append, xs, ys, List.mem_map,
        Finset.mem_sort, mem_firstBlock, mem_secondBlock]
      constructor
      · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
        · exact (block_ne j i he).elim
        · simpa only [he] using hj
      · intro hi
        exact Or.inr ⟨i, hi, rfl⟩
  change S.sort (· ≤ ·) = xs ++ ys
  calc
    S.sort (· ≤ ·) = (xs ++ ys).toFinset.sort (· ≤ ·) := congrArg (fun T : Finset (Fin (m + n)) => T.sort (· ≤ ·)) hset.symm
    _ = xs ++ ys := (List.toFinset_sort (· ≤ ·) hsorted.nodup).mpr hsorted.sortedLE.pairwise

private def alternatingSum {α R : Type*} [CommRing R] (w : α → R) : List α → R
  | [] => 0
  | a :: xs => -w a - alternatingSum w xs

private theorem alternatingSum_eq {α R : Type*} [CommRing R] (w : α → R)
    (xs : List α) : alternatingSum w xs =
      ∑ j : Fin xs.length, (-1 : R) ^ (j.val + 1) * w xs[j] := by
  induction xs with
  | nil => simp [alternatingSum]
  | cons a xs ih =>
    simp only [alternatingSum, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, zero_add, pow_one, neg_one_mul, Fin.val_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [pow_succ]

private theorem alternatingSum_append {α R : Type*} [CommRing R] (w : α → R)
    (xs ys : List α) : alternatingSum w (xs ++ ys) =
      alternatingSum w xs + (-1 : R) ^ xs.length * alternatingSum w ys := by
  induction xs with
  | nil => simp [alternatingSum]
  | cons a xs ih =>
    simp only [List.cons_append, alternatingSum, List.length_cons, ih, pow_succ]
    ring

private theorem alternatingSum_map {α β R : Type*} [CommRing R] (w : β → R)
    (f : α → β) (xs : List α) :
    alternatingSum w (xs.map f) = alternatingSum (w ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [alternatingSum, ih]

private theorem alternatingSum_mul {α R : Type*} [CommRing R] (w : α → R)
    (c : R) (xs : List α) :
    alternatingSum (fun a => w a * c) xs = alternatingSum w xs * c := by
  induction xs with
  | nil => simp [alternatingSum]
  | cons a xs ih => simp only [alternatingSum, ih]; ring

private theorem matchgateSum_eq_alternatingSum {s : ℕ} {R : Type*} [CommRing R]
    (G : SubsetSignature s R) (A B : Finset (Fin s)) (xs : List (Fin s)) :
    matchgateSum G A B xs = alternatingSum (fun i => G (A ∆ {i}) * G (B ∆ {i})) xs := by
  rw [alternatingSum_eq]
  unfold matchgateSum
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem xor_empty {s : ℕ} (S : Finset (Fin s)) : S ∆ ∅ = S := by
  ext i
  simp [Finset.mem_symmDiff]

/-- Tensoring two genuine MGI signatures preserves the full identities in the
consecutive boundary order, over any commutative ring. -/
theorem MatchgateIdentities.consecutiveTensor {m n : ℕ} {R : Type*} [CommRing R]
    {G : SubsetSignature m R} {H : SubsetSignature n R}
    (hG : MatchgateIdentities G) (hH : MatchgateIdentities H) :
    MatchgateIdentities (MatchgateWidth.consecutiveTensor G H) := by
  intro A B
  rw [sort_blocks, firstBlock_symmDiff, secondBlock_symmDiff,
    matchgateSum_eq_alternatingSum, alternatingSum_append,
    alternatingSum_map, alternatingSum_map]
  have hleft :
      (fun i : Fin m =>
        MatchgateWidth.consecutiveTensor G H (A ∆ {Fin.castAdd n i}) *
        MatchgateWidth.consecutiveTensor G H (B ∆ {Fin.castAdd n i})) =
      (fun i => (G (firstBlock A ∆ {i}) * G (firstBlock B ∆ {i})) *
        (H (secondBlock A) * H (secondBlock B))) := by
    funext i
    simp only [MatchgateWidth.consecutiveTensor, firstBlock_symmDiff, secondBlock_symmDiff,
      firstBlock_singleton_left, secondBlock_singleton_left]
    simp only [xor_empty]
    ring
  have hright :
      (fun i : Fin n =>
        MatchgateWidth.consecutiveTensor G H (A ∆ {Fin.natAdd m i}) *
        MatchgateWidth.consecutiveTensor G H (B ∆ {Fin.natAdd m i})) =
      (fun i => (H (secondBlock A ∆ {i}) * H (secondBlock B ∆ {i})) *
        (G (firstBlock A) * G (firstBlock B))) := by
    funext i
    simp only [MatchgateWidth.consecutiveTensor, firstBlock_symmDiff, secondBlock_symmDiff,
      firstBlock_singleton_right, secondBlock_singleton_right]
    simp only [xor_empty]
    ring
  change alternatingSum (fun i =>
      MatchgateWidth.consecutiveTensor G H (A ∆ {Fin.castAdd n i}) *
      MatchgateWidth.consecutiveTensor G H (B ∆ {Fin.castAdd n i})) _ + _ *
      alternatingSum (fun i =>
      MatchgateWidth.consecutiveTensor G H (A ∆ {Fin.natAdd m i}) *
      MatchgateWidth.consecutiveTensor G H (B ∆ {Fin.natAdd m i})) _ = 0
  rw [hleft, hright, alternatingSum_mul, alternatingSum_mul,
    ← matchgateSum_eq_alternatingSum, ← matchgateSum_eq_alternatingSum,
    hG, hH]
  simp

end MatchgateWidth
