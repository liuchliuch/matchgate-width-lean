import MatchgateWidth.ExteriorRank
import MatchgateWidth.PfaffianBlocks
import Mathlib.Data.Fin.Rev

/-!
# Cross-block Gaussian signatures and compound matrices

The external order here is all selected input modes in increasing order, followed
by all selected output modes in increasing order.  The resulting principal
Pfaffian is `(-1)^(p*(p-1)/2)` times the ordinary cross minor.  The paper instead
reverses the output order; that reversal has exactly the same triangular sign.
These are coordinate conventions, not claims that an unsigned wire permutation
is a valid matchgate transformation.
-/

namespace MatchgateWidth

noncomputable section

variable {R I J : Type*} [CommRing R]

/-- The actual skew matrix with only input-output cross couplings. -/
def gaussianCrossMatrix (B : Matrix I J R) : Matrix (I ⊕ J) (I ⊕ J) R
  | .inl _, .inl _ => 0
  | .inl i, .inr j => B i j
  | .inr j, .inl i => -B i j
  | .inr _, .inr _ => 0

@[simp] theorem gaussianCrossMatrix_inl_inl (B : Matrix I J R) (i i' : I) :
    gaussianCrossMatrix B (.inl i) (.inl i') = 0 := rfl
@[simp] theorem gaussianCrossMatrix_inl_inr (B : Matrix I J R) (i : I) (j : J) :
    gaussianCrossMatrix B (.inl i) (.inr j) = B i j := rfl
@[simp] theorem gaussianCrossMatrix_inr_inl (B : Matrix I J R) (i : I) (j : J) :
    gaussianCrossMatrix B (.inr j) (.inl i) = -B i j := rfl
@[simp] theorem gaussianCrossMatrix_inr_inr (B : Matrix I J R) (j j' : J) :
    gaussianCrossMatrix B (.inr j) (.inr j') = 0 := rfl

theorem gaussianCrossMatrix_skew (B : Matrix I J R) (x y : I ⊕ J) :
    gaussianCrossMatrix B x y = -gaussianCrossMatrix B y x := by
  cases x <;> cases y <;> simp

/-- Principal Pfaffian with inputs preceding outputs, in the supplied orders. -/
def gaussianCrossPfaffian (B : Matrix I J R) (xs : List I) (ys : List J) : R :=
  pfaffianList (gaussianCrossMatrix B) (xs.map Sum.inl ++ ys.map Sum.inr)

@[simp] theorem gaussianCrossPfaffian_nil_nil (B : Matrix I J R) :
    gaussianCrossPfaffian B [] [] = 1 := by simp [gaussianCrossPfaffian]

@[simp] theorem gaussianCrossPfaffian_nil_cons (B : Matrix I J R) (y : J) (ys : List J) :
    gaussianCrossPfaffian B [] (y :: ys) = 0 := by
  simp only [gaussianCrossPfaffian, List.map_nil, List.nil_append, List.map_cons]
  apply pfaffianList_isolated_first
  intro j
  simp

/-- The true Pfaffian recursion, with its zero same-side terms removed. -/
theorem gaussianCrossPfaffian_cons (B : Matrix I J R) (a : I)
    (xs : List I) (ys : List J) :
    gaussianCrossPfaffian B (a :: xs) ys =
      (-1 : R) ^ xs.length *
        ∑ j : Fin ys.length, (-1 : R) ^ j.val * B a ys[j] *
          gaussianCrossPfaffian B xs (ys.eraseIdx j.val) := by
  simp only [gaussianCrossPfaffian, List.map_cons, List.cons_append]
  rw [pfaffianList]
  let f : Fin (xs.map Sum.inl ++ ys.map Sum.inr).length → R := fun j =>
    (-1 : R) ^ j.val * gaussianCrossMatrix B (.inl a)
      (xs.map Sum.inl ++ ys.map Sum.inr)[j] *
      pfaffianList (gaussianCrossMatrix B)
        ((xs.map Sum.inl ++ ys.map Sum.inr).eraseIdx j.val)
  change (∑ j, f j) = _
  have hlen : (xs.map (Sum.inl : I → I ⊕ J) ++ ys.map Sum.inr).length =
      xs.length + ys.length := by simp
  rw [← Fin.sum_congr' f hlen.symm, Fin.sum_univ_add]
  have hleft : (∑ j : Fin xs.length, f ((Fin.castAdd ys.length j).cast hlen.symm)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    dsimp [f]
    rw [List.getElem_append_left (by simp)]
    simp
  rw [hleft, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [f]
  rw [List.getElem_append_right (by simp),
    List.eraseIdx_append_of_length_le (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem_map,
    gaussianCrossMatrix_inl_inr, List.eraseIdx_map, pow_add]
  ring

/-- Unequal numbers of selected input and output modes give zero. -/
theorem gaussianCrossPfaffian_eq_zero_of_length_ne (B : Matrix I J R)
    (xs : List I) (ys : List J) (h : xs.length ≠ ys.length) :
    gaussianCrossPfaffian B xs ys = 0 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact (h rfl).elim
    | cons y ys => simp
  | cons a xs ih =>
    rw [gaussianCrossPfaffian_cons]
    suffices (∑ j : Fin ys.length, (-1 : R) ^ j.val * B a ys[j] *
      gaussianCrossPfaffian B xs (ys.eraseIdx j.val)) = 0 by rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [ih]
    · simp
    · rw [List.length_eraseIdx_of_lt j.isLt]
      simp only [List.length_cons] at h
      have := j.isLt
      omega

/-- Deleting a coordinate from an `ofFn` list is the increasing skipped-index map. -/
theorem list_eraseIdx_ofFn_succAbove {α : Type*} {n : ℕ}
    (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    (List.ofFn f).eraseIdx j.val = List.ofFn (f ∘ j.succAbove) := by
  apply List.ext_getElem
  · rw [List.length_eraseIdx_of_lt (show j.val < (List.ofFn f).length by
      simpa only [List.length_ofFn] using j.isLt)]
    simp only [List.length_ofFn, Nat.add_sub_cancel]
  · intro i hi hi'
    rw [List.getElem_eraseIdx]
    split_ifs with hij
    · simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, hij]
    · simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, hij]

/-- The cross-block Pfaffian sign for `n` selected pairs. -/
def gaussianCrossSign (n : ℕ) : R := (-1 : R) ^ (n.choose 2)

@[simp] theorem gaussianCrossSign_zero : gaussianCrossSign (R := R) 0 = 1 := by
  simp [gaussianCrossSign]

theorem gaussianCrossSign_succ (n : ℕ) :
    gaussianCrossSign (R := R) (n + 1) = (-1 : R)^n * gaussianCrossSign n := by
  simp [gaussianCrossSign, Nat.choose_succ_succ, pow_add]

/-- The Pfaffian-determinant identity for the actual block matrix, proved by
its first-input recurrence and the determinant's first-row Laplace expansion. -/
theorem gaussianCrossPfaffian_ofFn (B : Matrix I J R) (n : ℕ)
    (x : Fin n → I) (y : Fin n → J) :
    gaussianCrossPfaffian B (List.ofFn x) (List.ofFn y) =
      gaussianCrossSign n * (B.submatrix x y).det := by
  induction n with
  | zero => simp [List.ofFn_zero, Matrix.det_isEmpty]
  | succ n ih =>
    rw [List.ofFn_succ (f := x), gaussianCrossPfaffian_cons]
    simp only [List.length_ofFn]
    rw [gaussianCrossSign_succ, Matrix.det_succ_row_zero]
    simp only [mul_assoc, Finset.mul_sum]
    apply Fintype.sum_equiv (finCongr List.length_ofFn)
    intro j
    let k : Fin (n + 1) := j.cast List.length_ofFn
    simp only [Fin.getElem_fin]
    have he := list_eraseIdx_ofFn_succAbove y k
    simp only [k, Fin.val_cast] at he
    rw [List.getElem_ofFn, he, ih]
    change (-1 : R)^n * ((-1)^k.val * (B (x 0) (y k) *
      (gaussianCrossSign n * (B.submatrix (fun i => x i.succ) (y ∘ k.succAbove)).det))) =
      (-1)^n * (gaussianCrossSign n * ((-1)^k.val *
        (B.submatrix x y 0 k * ((B.submatrix x y).submatrix Fin.succ k.succAbove).det)))
    simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_def]
    ring


/-- Reversing an enumerated list is precomposition with the finite reversal. -/
theorem list_reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (f ∘ Fin.revPerm) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn,
      Function.comp_apply, Fin.revPerm_apply]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- The finite reversal contributes precisely the triangular permutation sign. -/
theorem sign_finRev (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm (n := n)) = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  have hinner (j : Fin n) :
      (∏ i ∈ Finset.Iio j, if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1) =
        (-1 : ℤˣ) ^ j.val := by
    rw [← Fin.card_Iio j, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i < j := Finset.mem_Iio.mp hi
    simp only [Fin.revPerm_apply, Fin.rev_lt_rev, ite_eq_right (not_lt_of_ge hij.le)]
  simp_rw [hinner]
  rw [Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n, Finset.sum_range_id]

/-- In the source's planar convention, selected outputs are reversed.  Their
permutation sign cancels the cross-Pfaffian sign, giving the unsigned minor. -/
theorem gaussianCrossPfaffian_ofFn_reverse (B : Matrix I J R) (n : ℕ)
    (x : Fin n → I) (y : Fin n → J) :
    gaussianCrossPfaffian B (List.ofFn x) (List.ofFn y).reverse =
      (B.submatrix x y).det := by
  rw [list_reverse_ofFn, gaussianCrossPfaffian_ofFn]
  have hminor : B.submatrix x (y ∘ Fin.revPerm) =
      (B.submatrix x y).submatrix id Fin.revPerm := rfl
  rw [hminor, Matrix.det_permute', sign_finRev]
  simp only [gaussianCrossSign, Nat.choose_two_right, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← mul_assoc, ← pow_two, ← pow_mul, Nat.mul_comm _ 2, pow_mul, neg_one_sq]
  simp

section Subsets
variable [LinearOrder I] [LinearOrder J]

/-- Canonical increasing enumeration of a finite subset. -/
def gaussianSubsetList (s : Finset I) : List I :=
  List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))

@[simp] theorem gaussianSubsetList_length (s : Finset I) :
    (gaussianSubsetList s).length = s.card := List.length_ofFn

theorem gaussianSubsetList_ofCard (n : ℕ) (s : Set.powersetCard I n) :
    gaussianSubsetList (s : Finset I) =
      List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  rcases s with ⟨s, hs⟩
  have hc : s.card = n := Set.powersetCard.mem_iff.mp hs
  subst n
  rfl

/-- Subset-indexed actual Gaussian/Pfaffian signature matrix. -/
def gaussianPfaffianMatrix (B : Matrix I J R) : Matrix (Finset I) (Finset J) R :=
  fun s t => gaussianCrossPfaffian B (gaussianSubsetList s) (gaussianSubsetList t)

/-- Different-degree blocks of the actual signature vanish. -/
theorem gaussianPfaffianMatrix_apply_different_degree (B : Matrix I J R)
    (s : Finset I) (t : Finset J) (h : s.card ≠ t.card) :
    gaussianPfaffianMatrix B s t = 0 := by
  apply gaussianCrossPfaffian_eq_zero_of_length_ne
  simpa using h

/-- Equal-degree blocks are signed minors, with the sign from the actual
ordered Pfaffian recursion rather than a stipulated identity. -/
theorem gaussianPfaffianMatrix_apply_same_degree (n : ℕ) (B : Matrix I J R)
    (s : Set.powersetCard I n) (t : Set.powersetCard J n) :
    gaussianPfaffianMatrix B (s : Finset I) (t : Finset J) =
      (-1 : R) ^ (n * (n - 1) / 2) *
        (B.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  rw [gaussianPfaffianMatrix, gaussianSubsetList_ofCard, gaussianSubsetList_ofCard,
    gaussianCrossPfaffian_ofFn, gaussianCrossSign, Nat.choose_two_right]


/-- Actual principal-Pfaffian signature using increasing selected inputs and
reversed increasing selected outputs, matching the source's planar convention. -/
def gaussianPlanarPfaffianMatrix (B : Matrix I J R) : Matrix (Finset I) (Finset J) R :=
  fun s t => gaussianCrossPfaffian B (gaussianSubsetList s) (gaussianSubsetList t).reverse

theorem gaussianPlanarPfaffianMatrix_apply_different_degree (B : Matrix I J R)
    (s : Finset I) (t : Finset J) (h : s.card ≠ t.card) :
    gaussianPlanarPfaffianMatrix B s t = 0 := by
  apply gaussianCrossPfaffian_eq_zero_of_length_ne
  simpa using h

/-- In the planar output-reversal convention, the Pfaffian entry is exactly
the ordinary minor, with both order signs proved and cancelled. -/
theorem gaussianPlanarPfaffianMatrix_apply_same_degree (n : ℕ) (B : Matrix I J R)
    (s : Set.powersetCard I n) (t : Set.powersetCard J n) :
    gaussianPlanarPfaffianMatrix B (s : Finset I) (t : Finset J) =
      (B.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  rw [gaussianPlanarPfaffianMatrix, gaussianSubsetList_ofCard, gaussianSubsetList_ofCard,
    gaussianCrossPfaffian_ofFn_reverse]

end Subsets

section Rank
variable {K : Type*} [Field K] [Fintype I] [Fintype J]
  [LinearOrder I] [LinearOrder J]

/-- Exact entrywise Gaussian-to-compound identification. -/
theorem gaussianPfaffianMatrix_apply (B : Matrix I J K) (s : Finset I) (t : Finset J) :
    gaussianPfaffianMatrix B s t = gaussianCrossSign s.card * exteriorCompoundMatrix B s t := by
  by_cases h : s.card = t.card
  · let s' : Set.powersetCard I s.card := Set.powersetCard.ofCard rfl
    let t' : Set.powersetCard J s.card := Set.powersetCard.ofCard h.symm
    have hs : (s' : Finset I) = s := rfl
    have ht : (t' : Finset J) = t := rfl
    rw [← hs, ← ht, gaussianPfaffianMatrix_apply_same_degree s.card B s' t',
      exteriorCompoundMatrix_apply_same_degree s.card B s' t', exteriorPowerMatrix_apply]
    simp only [hs, gaussianCrossSign, Nat.choose_two_right]
  · rw [gaussianPfaffianMatrix_apply_different_degree B s t h,
      exteriorCompoundMatrix_apply_different_degree B s t h, mul_zero]

/-- The actual signature matrix differs from the full compound matrix only
by an explicitly invertible diagonal matrix of row signs. -/
theorem gaussianPfaffianMatrix_eq_diagonal_mul (B : Matrix I J K) :
    gaussianPfaffianMatrix B =
      Matrix.diagonal (fun s : Finset I => gaussianCrossSign s.card) * exteriorCompoundMatrix B := by
  classical
  ext s t
  rw [Matrix.diagonal_mul, gaussianPfaffianMatrix_apply]

/-- Rank of the actual subset-indexed Pfaffian signature.  Neither the
Pfaffian/minor identity nor any rank premise is assumed. -/
theorem gaussianPfaffianMatrix_rank (B : Matrix I J K) :
    (gaussianPfaffianMatrix B).rank = 2 ^ B.rank := by
  classical
  rw [gaussianPfaffianMatrix_eq_diagonal_mul,
    Matrix.rank_mul_eq_right_of_det_ne_zero, exteriorCompoundMatrix_rank]
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun s _ => by simp [gaussianCrossSign])


/-- The source-ordered actual Pfaffian signature is literally the full compound
matrix.  This identifies coordinates only; it asserts no wire transformation. -/
theorem gaussianPlanarPfaffianMatrix_eq_exteriorCompoundMatrix (B : Matrix I J K) :
    gaussianPlanarPfaffianMatrix B = exteriorCompoundMatrix B := by
  ext s t
  by_cases h : s.card = t.card
  · let s' : Set.powersetCard I s.card := Set.powersetCard.ofCard rfl
    let t' : Set.powersetCard J s.card := Set.powersetCard.ofCard h.symm
    have hs : (s' : Finset I) = s := rfl
    have ht : (t' : Finset J) = t := rfl
    rw [← hs, ← ht, gaussianPlanarPfaffianMatrix_apply_same_degree s.card B s' t',
      exteriorCompoundMatrix_apply_same_degree s.card B s' t', exteriorPowerMatrix_apply]
  · rw [gaussianPlanarPfaffianMatrix_apply_different_degree B s t h,
      exteriorCompoundMatrix_apply_different_degree B s t h]

/-- Rank of the actual Pfaffian signature with the planar output reversal. -/
theorem gaussianPlanarPfaffianMatrix_rank (B : Matrix I J K) :
    (gaussianPlanarPfaffianMatrix B).rank = 2 ^ B.rank := by
  rw [gaussianPlanarPfaffianMatrix_eq_exteriorCompoundMatrix, exteriorCompoundMatrix_rank]

/-- Rank two in the source-ordered Gaussian chart forces cross rank one. -/
theorem gaussianPlanarPfaffianMatrix_rank_two_iff (B : Matrix I J K) :
    (gaussianPlanarPfaffianMatrix B).rank = 2 ↔ B.rank = 1 := by
  rw [gaussianPlanarPfaffianMatrix_eq_exteriorCompoundMatrix]
  exact exteriorCompoundMatrix_rank_two_iff B

/-- Cross rank two gives a rank-four actual source-ordered Gaussian signature. -/
theorem gaussianPlanarPfaffianMatrix_rank_four_iff (B : Matrix I J K) :
    (gaussianPlanarPfaffianMatrix B).rank = 4 ↔ B.rank = 2 := by
  rw [gaussianPlanarPfaffianMatrix_eq_exteriorCompoundMatrix]
  exact exteriorCompoundMatrix_rank_four_iff B

/-- The rank-two actual Gaussian signature forces a rank-one cross matrix. -/
theorem gaussianPfaffianMatrix_rank_two_iff (B : Matrix I J K) :
    (gaussianPfaffianMatrix B).rank = 2 ↔ B.rank = 1 := by
  rw [gaussianPfaffianMatrix_rank]
  change 2 ^ B.rank = 2 ^ 1 ↔ B.rank = 1
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff

/-- Reindexing signature coordinates by genuine bijections preserves rank.
This is a linear-algebra statement, not an unsigned matchgate-wire operation. -/
theorem gaussianPfaffianMatrix_reindex_rank {S T : Type*} [Fintype T]
    (B : Matrix I J K) (e : S ≃ Finset I) (f : T ≃ Finset J) :
    ((gaussianPfaffianMatrix B).submatrix e f).rank = 2 ^ B.rank := by
  rw [Matrix.rank_submatrix, gaussianPfaffianMatrix_rank]

end Rank

end
end MatchgateWidth
