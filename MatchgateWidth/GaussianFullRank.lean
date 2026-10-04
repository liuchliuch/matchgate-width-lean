import MatchgateWidth.GaussianInputElimination

/-!
# Gaussian rank with both quadratic blocks

Changing the input block preserves the row space with an arbitrary fixed output
block. Exact ordered-Pfaffian reversal and transpose bookkeeping then remove the
output block as well. These are algebraic coefficient identities, not claims of
planar graph realization.
-/

namespace MatchgateWidth

noncomputable section

variable {R I J : Type*} [CommRing R]

/-- The full skew Gaussian block matrix before hypotheses are imposed. -/
def gaussianFullMatrix (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R) :
    Matrix (I ⊕ J) (I ⊕ J) R
  | .inl i, .inl i' => A i i'
  | .inl i, .inr j => B i j
  | .inr j, .inl i => -B i j
  | .inr j, .inr j' => D j j'

@[simp] theorem gaussianFullMatrix_output_zero (A : Matrix I I R) (B : Matrix I J R) :
    gaussianFullMatrix A B 0 = gaussianInputMatrix A B := by
  ext x y
  cases x <;> cases y <;> rfl

/-- Actual principal-Pfaffian coefficients, in the supplied orders. -/
def gaussianFullPfaffian (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (xs : List I) (ys : List J) : R :=
  pfaffianList (gaussianFullMatrix A B D) (xs.map Sum.inl ++ ys.map Sum.inr)

@[simp] theorem gaussianFullPfaffian_output_zero (A : Matrix I I R) (B : Matrix I J R)
    (xs : List I) (ys : List J) :
    gaussianFullPfaffian A B 0 xs ys = gaussianInputPfaffian A B xs ys := by
  simp [gaussianFullPfaffian, gaussianInputPfaffian]

/-- The empty input row is the complete output-block Pfaffian. -/
@[simp] theorem gaussianFullPfaffian_nil (A : Matrix I I R) (B : Matrix I J R)
    (D : Matrix J J R) (ys : List J) :
    gaussianFullPfaffian A B D [] ys = pfaffianList D ys := by
  simp only [gaussianFullPfaffian, List.map_nil, List.nil_append, pfaffianList_map]
  rfl

/-- First-input recursion, splitting internal and cross pairings. -/
theorem gaussianFullPfaffian_cons (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (a : I) (xs : List I) (ys : List J) :
    gaussianFullPfaffian A B D (a :: xs) ys =
      (∑ j : Fin xs.length, (-1 : R)^j.val * A a xs[j] *
        gaussianFullPfaffian A B D (xs.eraseIdx j.val) ys) +
      (-1 : R)^xs.length * gaussianOutputDeletion (B a) (gaussianFullPfaffian A B D xs) ys := by
  simp only [gaussianFullPfaffian, List.map_cons, List.cons_append]
  rw [pfaffianList]
  let f : Fin (xs.map Sum.inl ++ ys.map Sum.inr).length → R := fun j =>
    (-1 : R)^j.val * gaussianFullMatrix A B D (.inl a)
      (xs.map Sum.inl ++ ys.map Sum.inr)[j] *
      pfaffianList (gaussianFullMatrix A B D)
        ((xs.map Sum.inl ++ ys.map Sum.inr).eraseIdx j.val)
  change (∑ j, f j) = _
  have hlen : (xs.map (Sum.inl : I → I ⊕ J) ++ ys.map Sum.inr).length =
      xs.length + ys.length := by simp
  rw [← Fin.sum_congr' f hlen.symm, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    rw [List.getElem_append_left (by simp), List.eraseIdx_append_of_lt_length (by simp)]
    simp [gaussianFullMatrix, List.eraseIdx_map]
  · change (∑ j : Fin ys.length, f ((Fin.natAdd xs.length j).cast hlen.symm)) =
      (-1 : R)^xs.length * ∑ j : Fin ys.length, _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    rw [List.getElem_append_right (by simp), List.eraseIdx_append_of_length_le (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem_map,
      gaussianFullMatrix, List.eraseIdx_map, pow_add, gaussianFullPfaffian]
    ring

/-- Span of ordered input rows, with output-list coordinates. This intermediate
space avoids making any unproved permutation claim about matchgate wires. -/
def gaussianFullListRowSpan (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R) :
    Submodule R (List J → R) :=
  Submodule.span R (Set.range (gaussianFullPfaffian A B D))

theorem gaussianFullPfaffian_mem_listRowSpan (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (xs : List I) : gaussianFullPfaffian A B D xs ∈ gaussianFullListRowSpan A B D :=
  Submodule.subset_span ⟨xs, rfl⟩

/-- Each signed output-deletion operator preserves the actual Gaussian row span. -/
theorem gaussianFullListRowSpan_deletion (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (a : I) (F : List J → R) (hF : F ∈ gaussianFullListRowSpan A B D) :
    gaussianOutputDeletion (B a) F ∈ gaussianFullListRowSpan A B D := by
  apply Submodule.span_induction (p := fun F _ =>
      gaussianOutputDeletion (B a) F ∈ gaussianFullListRowSpan A B D) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨xs, rfl⟩
    have hrec : gaussianOutputDeletion (B a) (gaussianFullPfaffian A B D xs) =
        (-1 : R)^xs.length • (gaussianFullPfaffian A B D (a :: xs) -
          ∑ j : Fin xs.length, ((-1 : R)^j.val * A a xs[j]) •
            gaussianFullPfaffian A B D (xs.eraseIdx j.val)) := by
      ext ys
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply,
        gaussianFullPfaffian_cons]
      have hs : (-1 : R)^xs.length * (-1 : R)^xs.length = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc
        _ = ((-1 : R)^xs.length * (-1 : R)^xs.length) *
            gaussianOutputDeletion (B a) (gaussianFullPfaffian A B D xs) ys := by rw [hs, one_mul]
        _ = _ := by ring
    rw [hrec]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact gaussianFullPfaffian_mem_listRowSpan A B D (a :: xs)
    · apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (gaussianFullPfaffian_mem_listRowSpan A B D _)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hx' hy'
    simpa only [map_add] using Submodule.add_mem _ hx' hy'
  · intro c x hx hx'
    simpa only [map_smul] using Submodule.smul_mem _ c hx'

/-- Every row for any other input block lies in the original ordered row span. -/
theorem gaussianFullPfaffian_mem_other_listRowSpan
    (A A' : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R) (xs : List I) :
    gaussianFullPfaffian A' B D xs ∈ gaussianFullListRowSpan A B D := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil =>
      have he : gaussianFullPfaffian A' B D [] = gaussianFullPfaffian A B D [] := by
        ext ys
        simp
      rw [he]
      exact gaussianFullPfaffian_mem_listRowSpan A B D []
    | cons a xs =>
      have he : gaussianFullPfaffian A' B D (a :: xs) =
          (∑ j : Fin xs.length, ((-1 : R)^j.val * A' a xs[j]) •
            gaussianFullPfaffian A' B D (xs.eraseIdx j.val)) +
          (-1 : R)^xs.length • gaussianOutputDeletion (B a) (gaussianFullPfaffian A' B D xs) := by
        ext ys
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          gaussianFullPfaffian_cons]
      rw [he]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro j _
        apply Submodule.smul_mem
        apply ih
        have := List.length_eraseIdx_le xs j.val
        change (xs.eraseIdx j.val).length < (a :: xs).length
        simp only [List.length_cons]
        omega
      · apply Submodule.smul_mem
        exact gaussianFullListRowSpan_deletion A B D a _ (ih xs (by change xs.length < (a :: xs).length; simp))

/-- Changing the input-input block preserves the row space at the level of
ordered-list coefficients, proved directly from the Pfaffian recursion. -/
theorem gaussianFullListRowSpan_eq (A A' : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R) :
    gaussianFullListRowSpan A B D = gaussianFullListRowSpan A' B D := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨xs, rfl⟩
    exact gaussianFullPfaffian_mem_other_listRowSpan A' A B D xs
  · rintro _ ⟨xs, rfl⟩
    exact gaussianFullPfaffian_mem_other_listRowSpan A A' B D xs


/-- Skew diagonal blocks give a skew full Gaussian matrix. -/
theorem gaussianFullMatrix_skew (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j) (x y : I ⊕ J) :
    gaussianFullMatrix A B D x y = -gaussianFullMatrix A B D y x := by
  cases x <;> cases y
  · exact hA _ _
  · simp [gaussianFullMatrix]
  · rfl
  · exact hD _ _

/-- Reversing an interior list contributes its triangular sign, uniformly in
all surrounding coordinates. -/
theorem pfaffianList_reverse_sign {ι : Type*} (M : Matrix ι ι R)
    (hM : ∀ x y, M x y = -M y x) (xs pre suf : List ι) :
    pfaffianList M (pre ++ xs ++ suf) =
      (-1 : R) ^ (xs.length.choose 2) * pfaffianList M (pre ++ xs.reverse ++ suf) := by
  induction xs generalizing pre with
  | nil => simp
  | cons a xs ih =>
    have hi := ih (pre ++ [a])
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hi
    simp only [List.append_assoc, List.cons_append]
    rw [hi]
    rw [pfaffianList_move_right M hM a xs.reverse pre suf]
    simp only [List.length_cons, List.length_reverse, List.reverse_cons,
      List.append_assoc, List.singleton_append, Nat.choose_succ_succ,
      Nat.choose_one_right, pow_add]
    ring

/-- Scaling every matrix entry scales an ordered Pfaffian by half its degree;
odd-degree coefficients vanish, so the floor formula also holds there. -/
theorem pfaffianList_scale {ι : Type*} (M : Matrix ι ι R) (c : R) (xs : List ι) :
    pfaffianList (fun x y => c * M x y) xs =
      c ^ (xs.length / 2) * pfaffianList M xs := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil =>
      rw [pfaffianList_nil (fun x y => c * M x y), pfaffianList_nil]
      simp
    | cons a xs =>
      rw [pfaffianList.eq_2 (fun x y => c * M x y) a xs, pfaffianList.eq_2 M a xs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj := j.isLt
      have he : (xs.eraseIdx j.val).length = xs.length - 1 :=
        List.length_eraseIdx_of_lt hj
      have hlt : (xs.eraseIdx j.val).length < (a :: xs).length := by
        simp only [List.length_cons]
        omega
      have hd : (a :: xs).length / 2 = (xs.eraseIdx j.val).length / 2 + 1 := by
        simp only [List.length_cons]
        omega
      rw [ih _ hlt, hd, pow_succ]
      ring

/-- The signs from negating an even-degree matrix and reversing all coordinates
cancel. Odd-degree coefficients vanish automatically. -/
theorem pfaffianList_neg_reverse {ι : Type*} (M : Matrix ι ι R)
    (hM : ∀ x y, M x y = -M y x) (xs : List ι) :
    pfaffianList (-M) xs.reverse = pfaffianList M xs := by
  have hn : (-M : Matrix ι ι R) = fun x y => (-1 : R) * M x y := by ext x y; simp
  rw [hn, pfaffianList_scale, List.length_reverse]
  have hr := pfaffianList_reverse_sign M hM xs.reverse [] []
  simp only [List.nil_append, List.append_nil, List.reverse_reverse,
    List.length_reverse] at hr
  rw [hr, ← mul_assoc, ← pow_add]
  by_cases ho : xs.length % 2 = 1
  · rw [pfaffianList_odd M xs ho, mul_zero]
  · have he : Even xs.length := by
      rw [Nat.even_iff]
      omega
    obtain ⟨k, hk⟩ := he
    have hs : Even (xs.length / 2 + xs.length.choose 2) := by
      refine ⟨k * k, ?_⟩
      rw [hk, Nat.choose_two_right]
      have hkk : k + k = 2 * k := by omega
      rw [hkk]
      have hdiv : 2 * k / 2 = k := by omega
      rw [hdiv]
      by_cases hk0 : k = 0
      · subst k; simp
      · have heq : 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) := by ring
        rw [heq, Nat.mul_div_right _ (by decide : 0 < 2)]
        have ht : 2 * k - 1 + 1 = 2 * k := by omega
        nlinarith
    rw [hs.neg_one_pow, one_mul]

/-- Swapping the input/output roles reverses the full mode order. Negating
both quadratic blocks makes that reversal cancel exactly, with no residual sign. -/
theorem gaussianFullPfaffian_swap (A : Matrix I I R) (B : Matrix I J R)
    (D : Matrix J J R) (hA : ∀ i i', A i i' = -A i' i)
    (hD : ∀ j j', D j j' = -D j' j) (xs : List I) (ys : List J) :
    gaussianFullPfaffian (-D) B.transpose (-A) ys xs.reverse =
      gaussianFullPfaffian A B D xs ys.reverse := by
  let M := gaussianFullMatrix A B D
  let N := gaussianFullMatrix (-D) B.transpose (-A)
  let zs := xs.map Sum.inl ++ ys.reverse.map Sum.inr
  have hlist : ys.map Sum.inl ++ xs.reverse.map Sum.inr = zs.reverse.map Sum.swap := by
    simp [zs, List.reverse_append, List.map_append, List.map_reverse,
      List.map_map, Function.comp_def]
  change pfaffianList N (ys.map Sum.inl ++ xs.reverse.map Sum.inr) = pfaffianList M zs
  rw [hlist, pfaffianList_map]
  have hmatrix : (fun x y => N (Sum.swap x) (Sum.swap y)) = -M := by
    funext x y
    cases x <;> cases y <;> simp [M, N, gaussianFullMatrix, Matrix.transpose_apply]
  rw [hmatrix]
  exact pfaffianList_neg_reverse M (gaussianFullMatrix_skew A B D hA hD) zs

section Subsets

variable [LinearOrder I] [LinearOrder J]

/-- Actual subset-indexed Gaussian signature with both quadratic blocks.
Outputs are reversed after increasing enumeration, as in the planar cross chart. -/
def gaussianFullPlanarPfaffianMatrix (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R) :
    Matrix (Finset I) (Finset J) R :=
  fun s t => gaussianFullPfaffian A B D (gaussianSubsetList s) (gaussianSubsetList t).reverse

@[simp] theorem gaussianFullPlanarPfaffianMatrix_output_zero
    (A : Matrix I I R) (B : Matrix I J R) :
    gaussianFullPlanarPfaffianMatrix A B 0 = gaussianInputPlanarPfaffianMatrix A B := by
  ext s t
  simp [gaussianFullPlanarPfaffianMatrix, gaussianInputPlanarPfaffianMatrix]

/-- Exact transpose bookkeeping for the source's fixed planar ordering. -/
theorem gaussianFullPlanarPfaffianMatrix_transpose
    (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j) :
    (gaussianFullPlanarPfaffianMatrix A B D).transpose =
      gaussianFullPlanarPfaffianMatrix (-D) B.transpose (-A) := by
  ext t s
  exact (gaussianFullPfaffian_swap A B D hA hD
    (gaussianSubsetList s) (gaussianSubsetList t)).symm

/-- All ordered input rows reduce to the true finite-subset row span. -/
theorem gaussianFullListRowSpan_evaluate [NoZeroDivisors R] [CharZero R]
    (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j)
    (F : List J → R) (hF : F ∈ gaussianFullListRowSpan A B D) :
    gaussianPlanarOutputEvaluation F ∈
      Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D).row) := by
  apply Submodule.span_induction (p := fun F _ =>
      gaussianPlanarOutputEvaluation F ∈
        Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D).row))
      ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨xs, rfl⟩
    obtain ⟨c, hc⟩ := pfaffianList_input_normalization (gaussianFullMatrix A B D)
      (gaussianFullMatrix_skew A B D hA hD) xs
    have he : gaussianPlanarOutputEvaluation (gaussianFullPfaffian A B D xs) =
        c • (gaussianFullPlanarPfaffianMatrix A B D).row xs.toFinset := by
      ext t
      exact hc (gaussianSubsetList t).reverse
    rw [he]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨xs.toFinset, rfl⟩)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hx' hy'
    simpa only [map_add] using Submodule.add_mem _ hx' hy'
  · intro c x hx hx'
    simpa only [map_smul] using Submodule.smul_mem _ c hx'

/-- Changing a skew input-input block preserves the row span of the actual
subset Pfaffian matrix. No generating-function coefficient identity is assumed. -/
theorem gaussianFullPlanarPfaffianMatrix_rowSpan_eq [NoZeroDivisors R] [CharZero R]
    (A A' : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hA' : ∀ i i', A' i i' = -A' i' i)
    (hD : ∀ j j', D j j' = -D j' j) :
    Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D).row) =
      Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A' B D).row) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨s, rfl⟩
    exact gaussianFullListRowSpan_evaluate A' B D hA' hD _
      (gaussianFullPfaffian_mem_other_listRowSpan A' A B D (gaussianSubsetList s))
  · rintro _ ⟨s, rfl⟩
    exact gaussianFullListRowSpan_evaluate A B D hA hD _
      (gaussianFullPfaffian_mem_other_listRowSpan A A' B D (gaussianSubsetList s))


/-- The row-space normal form eliminates only the input quadratic block;
the fixed output quadratic block remains in the coordinate functions. -/
theorem gaussianFullPlanarPfaffianMatrix_rowSpan_normalForm [NoZeroDivisors R] [CharZero R]
    (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j) :
    Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D).row) =
      Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix 0 B D).row) :=
  gaussianFullPlanarPfaffianMatrix_rowSpan_eq A 0 B D hA (by simp) hD

/-- Changing the output quadratic block preserves the actual column space.
This is the transpose of input elimination with its signs fully accounted for. -/
theorem gaussianFullPlanarPfaffianMatrix_colSpan_eq [NoZeroDivisors R] [CharZero R]
    (A : Matrix I I R) (B : Matrix I J R) (D D' : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j)
    (hD' : ∀ j j', D' j j' = -D' j' j) :
    Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D).col) =
      Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D').col) := by
  rw [← Matrix.row_transpose, ← Matrix.row_transpose,
    gaussianFullPlanarPfaffianMatrix_transpose A B D hA hD,
    gaussianFullPlanarPfaffianMatrix_transpose A B D' hA hD']
  apply gaussianFullPlanarPfaffianMatrix_rowSpan_eq
  · intro j j'; simpa using congrArg Neg.neg (hD j j')
  · intro j j'; simpa using congrArg Neg.neg (hD' j j')
  · intro i i'; simpa using congrArg Neg.neg (hA i i')

/-- Column-space normal form obtained by removing the output quadratic block. -/
theorem gaussianFullPlanarPfaffianMatrix_colSpan_normalForm [NoZeroDivisors R] [CharZero R]
    (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j) :
    Submodule.span R (Set.range (gaussianFullPlanarPfaffianMatrix A B D).col) =
      Submodule.span R (Set.range (gaussianInputPlanarPfaffianMatrix A B).col) := by
  simpa only [gaussianFullPlanarPfaffianMatrix_output_zero] using
    gaussianFullPlanarPfaffianMatrix_colSpan_eq A B D 0 hA hD (by simp)

end Subsets

section Rank

variable {K : Type*} [Field K] [CharZero K] [Fintype I] [Fintype J]
  [LinearOrder I] [LinearOrder J]

/-- Full Gaussian rank rigidity: either local quadratic block can be arbitrary,
while the rank of the actual principal-Pfaffian matrix is fixed by the cross block. -/
theorem gaussianFullPlanarPfaffianMatrix_rank
    (A : Matrix I I K) (B : Matrix I J K) (D : Matrix J J K)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j) :
    (gaussianFullPlanarPfaffianMatrix A B D).rank = 2 ^ B.rank := by
  rw [Matrix.rank_eq_finrank_span_row,
    gaussianFullPlanarPfaffianMatrix_rowSpan_normalForm A B D hA hD,
    ← Matrix.rank_eq_finrank_span_row,
    ← Matrix.rank_transpose (gaussianFullPlanarPfaffianMatrix 0 B D),
    gaussianFullPlanarPfaffianMatrix_transpose 0 B D (by simp) hD,
    neg_zero, gaussianFullPlanarPfaffianMatrix_output_zero,
    gaussianInputPlanarPfaffianMatrix_rank]
  · rw [Matrix.rank_transpose]
  · intro j j'
    simp only [Matrix.neg_apply]
    rw [hD]

/-- Rank two is equivalent to a rank-one cross block, without assuming that
either local quadratic block vanishes. -/
theorem gaussianFullPlanarPfaffianMatrix_rank_two_iff
    (A : Matrix I I K) (B : Matrix I J K) (D : Matrix J J K)
    (hA : ∀ i i', A i i' = -A i' i) (hD : ∀ j j', D j j' = -D j' j) :
    (gaussianFullPlanarPfaffianMatrix A B D).rank = 2 ↔ B.rank = 1 := by
  rw [gaussianFullPlanarPfaffianMatrix_rank A B D hA hD]
  change 2 ^ B.rank = 2 ^ 1 ↔ B.rank = 1
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff

end Rank

end
end MatchgateWidth
