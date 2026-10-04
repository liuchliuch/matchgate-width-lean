import MatchgateWidth.MGIBlockContraction

/-! # Cyclic boundary rerooting of literal matchgate identities -/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff

private theorem cyclic_xor_common {n : ℕ} (A B C : Finset (Fin n)) :
    (A ∆ C) ∆ (B ∆ C) = A ∆ B := by
  ext i
  simp only [Finset.mem_symmDiff]
  tauto

/-- Coordinates at odd Hamming distance cannot both be nonzero. -/
theorem MatchgateIdentities.mul_eq_zero_of_odd_difference {n : ℕ} {K : Type*} [Field K]
    {F : SubsetSignature n K} (hF : MatchgateIdentities F)
    (A B : Finset (Fin n)) (ho : (A ∆ B).card % 2 = 1) : F A * F B = 0 := by
  by_cases ha : F A = 0
  · simp [ha]
  have h0 : MatchgateWidth.subsetPivot F A ∅ ≠ 0 := by
    change F (⊥ ∆ A) ≠ 0
    simpa only [bot_symmDiff] using ha
  have h := (hF.subsetPivot A).odd_eq_zero h0 (B ∆ A) (by simpa [symmDiff_comm] using ho)
  simpa [MatchgateWidth.subsetPivot] using congrArg (fun z => F A * z) h

private def cyclicAlt {α R : Type*} [CommRing R] (w : α → R) : List α → R
  | [] => 0
  | i :: xs => -w i - cyclicAlt w xs

private theorem cyclicAlt_eq {α R : Type*} [CommRing R] (w : α → R) (xs : List α) :
    cyclicAlt w xs = ∑ j : Fin xs.length, (-1 : R) ^ (j.val + 1) * w xs[j] := by
  induction xs with
  | nil => simp [cyclicAlt]
  | cons a xs ih =>
    simp only [cyclicAlt, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, zero_add, pow_one, neg_one_mul, Fin.val_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [pow_succ]

private theorem cyclicAlt_append {α R : Type*} [CommRing R]
    (w : α → R) (xs ys : List α) :
    cyclicAlt w (xs ++ ys) = cyclicAlt w xs + (-1 : R)^xs.length * cyclicAlt w ys := by
  induction xs with
  | nil => simp [cyclicAlt]
  | cons a xs ih => simp only [cyclicAlt, List.cons_append, List.length_cons, ih, pow_succ]; ring

private theorem cyclicAlt_map {α β R : Type*} [CommRing R]
    (w : β → R) (f : α → β) (xs : List α) :
    cyclicAlt w (xs.map f) = cyclicAlt (w ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [cyclicAlt, ih]

private theorem cyclic_sum_alt {n : ℕ} {R : Type*} [CommRing R]
    (F : SubsetSignature n R) (A B : Finset (Fin n)) (xs : List (Fin n)) :
    matchgateSum F A B xs = cyclicAlt (fun i => F (A ∆ {i}) * F (B ∆ {i})) xs := by
  rw [cyclicAlt_eq]
  unfold matchgateSum
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Move the first consecutive block to the end, preserving order within both. -/
def rotateBlocks {m n : ℕ} (S : Finset (Fin (n+m))) : Finset (Fin (m+n)) :=
  blockJoin (secondBlock S) (firstBlock S)

@[simp] theorem rotateBlocks_blockJoin {m n : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) :
    rotateBlocks (blockJoin A B) = blockJoin B A := by simp [rotateBlocks]

private theorem cyclic_blockJoin_blocks {m n : ℕ} (S : Finset (Fin (m+n))) :
    blockJoin (firstBlock S) (secondBlock S) = S := by
  ext i
  induction i using Fin.addCases with
  | left i => simpa only [← mem_firstBlock, firstBlock_blockJoin]
  | right i => simpa only [← mem_secondBlock, secondBlock_blockJoin]

@[simp] theorem blockJoin_card {m n : ℕ} (A : Finset (Fin m)) (B : Finset (Fin n)) :
    (blockJoin A B).card = A.card + B.card := by
  rw [blockJoin, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  apply Finset.disjoint_left.mpr
  intro x ha hb
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j,_,h⟩ := Finset.mem_map.mp hb
  have hv := congrArg Fin.val h
  change m + j.val = i.val at hv
  omega

private theorem cyclic_split {m n : ℕ} {K : Type*} [CommRing K]
    (F : SubsetSignature (m+n) K) (A C : Finset (Fin m)) (B D : Finset (Fin n)) :
    matchgateSum F (blockJoin A B) (blockJoin C D)
      (((blockJoin A B) ∆ (blockJoin C D)).sort (· ≤ ·)) =
    cyclicAlt (fun i => F (blockJoin (A ∆ {i}) B) * F (blockJoin (C ∆ {i}) D))
      ((A ∆ C).sort (· ≤ ·)) + (-1 : K)^(A ∆ C).card *
    cyclicAlt (fun j => F (blockJoin A (B ∆ {j})) * F (blockJoin C (D ∆ {j})))
      ((B ∆ D).sort (· ≤ ·)) := by
  rw [cyclic_sum_alt, blockJoin_symmDiff, sort_blocks]
  simp only [firstBlock_blockJoin, secondBlock_blockJoin, cyclicAlt_append,
    cyclicAlt_map, List.length_map, Finset.length_sort, Function.comp_def,
    blockJoin_flip_left, blockJoin_flip_right]

/-- Cyclic rerooting is valid at every cut, with no within-block reversal. -/
theorem MatchgateIdentities.rotateBlocks {m n : ℕ} {K : Type*} [Field K]
    {F : SubsetSignature (m+n) K} (hF : MatchgateIdentities F) :
    MatchgateIdentities (fun S => F (MatchgateWidth.rotateBlocks S)) := by
  intro U V
  obtain ⟨A,B,rfl⟩ : ∃ A B, U = blockJoin A B :=
    ⟨firstBlock U, secondBlock U, (cyclic_blockJoin_blocks U).symm⟩
  obtain ⟨C,D,rfl⟩ : ∃ C D, V = blockJoin C D :=
    ⟨firstBlock V, secondBlock V, (cyclic_blockJoin_blocks V).symm⟩
  rw [cyclic_split]
  simp only [rotateBlocks_blockJoin]
  have h := hF (blockJoin B A) (blockJoin D C)
  rw [cyclic_split] at h
  let L := cyclicAlt (fun i => F (blockJoin (B ∆ {i}) A) * F (blockJoin (D ∆ {i}) C))
    ((B ∆ D).sort (· ≤ ·))
  let R := cyclicAlt (fun j => F (blockJoin B (A ∆ {j})) * F (blockJoin D (C ∆ {j})))
    ((A ∆ C).sort (· ≤ ·))
  change R + (-1 : K)^(A ∆ C).card * L = 0
  change L + (-1 : K)^(B ∆ D).card * R = 0 at h
  by_cases he : Even ((B ∆ D).card + (A ∆ C).card)
  · have hs : (-1 : K)^(A ∆ C).card * (-1 : K)^(B ∆ D).card = 1 := by
      rw [← pow_add, Nat.add_comm]
      exact he.neg_one_pow
    calc R + (-1 : K)^(A ∆ C).card * L =
        (-1 : K)^(A ∆ C).card * (L + (-1 : K)^(B ∆ D).card * R) := by rw [mul_add, ← mul_assoc, hs]; ring
      _ = 0 := by rw [h, mul_zero]
  · have ho : ((blockJoin B A) ∆ (blockJoin D C)).card % 2 = 1 := by
      rw [blockJoin_symmDiff, blockJoin_card]
      rw [Nat.even_iff] at he
      omega
    have hz (i : Fin (m+n)) :
        F (blockJoin B A ∆ {i}) * F (blockJoin D C ∆ {i}) = 0 :=
      hF.mul_eq_zero_of_odd_difference _ _ (by rwa [cyclic_xor_common])
    have hl : L = 0 := by
      dsimp [L]
      rw [cyclicAlt_eq]
      apply Finset.sum_eq_zero
      intro i _
      rw [← blockJoin_flip_left, ← blockJoin_flip_left, hz, mul_zero]
    have hr : R = 0 := by
      dsimp [R]
      rw [cyclicAlt_eq]
      apply Finset.sum_eq_zero
      intro i _
      rw [← blockJoin_flip_right, ← blockJoin_flip_right, hz, mul_zero]
    rw [hl, hr, mul_zero, add_zero]

/-- Boolean-coordinate form of the same cyclic cut rotation. -/
theorem BooleanMatchgateIdentities.rotateBlocks {m n : ℕ} {K : Type*} [Field K]
    {F : BooleanTable (m+n) K} (hF : BooleanMatchgateIdentities F) :
    BooleanMatchgateIdentities
      (fun z : BooleanInput (n+m) => F (fun i => z (finAddFlip i))) := by
  have heq (S : Finset (Fin (n+m))) :
      (booleanSubsetEquiv (m+n)).symm (MatchgateWidth.rotateBlocks S) =
        (fun i => (booleanSubsetEquiv (n+m)).symm S (finAddFlip i)) := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [booleanSubsetEquiv, Equiv.coe_fn_symm_mk, MatchgateWidth.rotateBlocks,
        finAddFlip_apply_castAdd]
      congr 1
      exact propext (by rw [← mem_firstBlock, firstBlock_blockJoin, mem_secondBlock])
    | right i =>
      simp only [booleanSubsetEquiv, Equiv.coe_fn_symm_mk, MatchgateWidth.rotateBlocks,
        finAddFlip_apply_natAdd]
      congr 1
      exact propext (by rw [← mem_secondBlock, secondBlock_blockJoin, mem_firstBlock])
  have h := MatchgateIdentities.rotateBlocks hF
  change MatchgateIdentities _
  simpa only [heq] using h

end
end MatchgateWidth
