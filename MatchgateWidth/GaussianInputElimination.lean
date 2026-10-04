import MatchgateWidth.GaussianCross
import MatchgateWidth.PfaffianRowNormalization

/-!
# Eliminating the input quadratic block

The proof uses the actual ordered Pfaffian recursion. Signed deletion on output
lists is a linear operator. The span of all ordered input rows is stable under
these operators, independently of the input-input block. Consequently changing
that block preserves the row span. Alternation then reduces the generators to
increasing input subsets; the selected output order is kept fixed throughout.
-/

namespace MatchgateWidth

noncomputable section

variable {R I J : Type*} [CommRing R]

/-- A Gaussian chart with arbitrary input-input couplings and zero output block. -/
def gaussianInputMatrix (A : Matrix I I R) (B : Matrix I J R) :
    Matrix (I ⊕ J) (I ⊕ J) R
  | .inl i, .inl i' => A i i'
  | .inl i, .inr j => B i j
  | .inr j, .inl i => -B i j
  | .inr _, .inr _ => 0

@[simp] theorem gaussianInputMatrix_zero (B : Matrix I J R) :
    gaussianInputMatrix 0 B = gaussianCrossMatrix B := by
  ext x y
  cases x <;> cases y <;> rfl

/-- Actual principal-Pfaffian coefficient, in the supplied input/output orders. -/
def gaussianInputPfaffian (A : Matrix I I R) (B : Matrix I J R)
    (xs : List I) (ys : List J) : R :=
  pfaffianList (gaussianInputMatrix A B) (xs.map Sum.inl ++ ys.map Sum.inr)

@[simp] theorem gaussianInputPfaffian_zero (B : Matrix I J R)
    (xs : List I) (ys : List J) :
    gaussianInputPfaffian 0 B xs ys = gaussianCrossPfaffian B xs ys := by
  simp [gaussianInputPfaffian, gaussianCrossPfaffian]

@[simp] theorem gaussianInputPfaffian_nil_nil (A : Matrix I I R) (B : Matrix I J R) :
    gaussianInputPfaffian A B [] [] = 1 := by simp [gaussianInputPfaffian]

@[simp] theorem gaussianInputPfaffian_nil_cons (A : Matrix I I R) (B : Matrix I J R)
    (y : J) (ys : List J) : gaussianInputPfaffian A B [] (y :: ys) = 0 := by
  simp only [gaussianInputPfaffian, List.map_nil, List.nil_append, List.map_cons]
  apply pfaffianList_isolated_first
  intro j
  simp [gaussianInputMatrix]

/-- Signed deletion in the output variables, directly as a linear operator. -/
def gaussianOutputDeletion (b : J → R) : (List J → R) →ₗ[R] (List J → R) where
  toFun F ys := ∑ j : Fin ys.length, (-1 : R)^j.val * b ys[j] * F (ys.eraseIdx j.val)
  map_add' F G := by
    ext ys
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c F := by
    ext ys
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- First-input recursion, splitting internal and cross pairings. -/
theorem gaussianInputPfaffian_cons (A : Matrix I I R) (B : Matrix I J R)
    (a : I) (xs : List I) (ys : List J) :
    gaussianInputPfaffian A B (a :: xs) ys =
      (∑ j : Fin xs.length, (-1 : R)^j.val * A a xs[j] *
        gaussianInputPfaffian A B (xs.eraseIdx j.val) ys) +
      (-1 : R)^xs.length * gaussianOutputDeletion (B a) (gaussianInputPfaffian A B xs) ys := by
  simp only [gaussianInputPfaffian, List.map_cons, List.cons_append]
  rw [pfaffianList]
  let f : Fin (xs.map Sum.inl ++ ys.map Sum.inr).length → R := fun j =>
    (-1 : R)^j.val * gaussianInputMatrix A B (.inl a)
      (xs.map Sum.inl ++ ys.map Sum.inr)[j] *
      pfaffianList (gaussianInputMatrix A B)
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
    simp [gaussianInputMatrix, List.eraseIdx_map]
  · change (∑ j : Fin ys.length, f ((Fin.natAdd xs.length j).cast hlen.symm)) =
      (-1 : R)^xs.length * ∑ j : Fin ys.length, _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    rw [List.getElem_append_right (by simp), List.eraseIdx_append_of_length_le (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem_map,
      gaussianInputMatrix, List.eraseIdx_map, pow_add, gaussianInputPfaffian]
    ring

/-- Span of ordered input rows, with output-list coordinates. This intermediate
space avoids making any unproved permutation claim about matchgate wires. -/
def gaussianInputListRowSpan (A : Matrix I I R) (B : Matrix I J R) :
    Submodule R (List J → R) :=
  Submodule.span R (Set.range (gaussianInputPfaffian A B))

theorem gaussianInputPfaffian_mem_listRowSpan (A : Matrix I I R) (B : Matrix I J R)
    (xs : List I) : gaussianInputPfaffian A B xs ∈ gaussianInputListRowSpan A B :=
  Submodule.subset_span ⟨xs, rfl⟩

/-- Each signed output-deletion operator preserves the actual Gaussian row span. -/
theorem gaussianInputListRowSpan_deletion (A : Matrix I I R) (B : Matrix I J R)
    (a : I) (F : List J → R) (hF : F ∈ gaussianInputListRowSpan A B) :
    gaussianOutputDeletion (B a) F ∈ gaussianInputListRowSpan A B := by
  apply Submodule.span_induction (p := fun F _ =>
      gaussianOutputDeletion (B a) F ∈ gaussianInputListRowSpan A B) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨xs, rfl⟩
    have hrec : gaussianOutputDeletion (B a) (gaussianInputPfaffian A B xs) =
        (-1 : R)^xs.length • (gaussianInputPfaffian A B (a :: xs) -
          ∑ j : Fin xs.length, ((-1 : R)^j.val * A a xs[j]) •
            gaussianInputPfaffian A B (xs.eraseIdx j.val)) := by
      ext ys
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply,
        gaussianInputPfaffian_cons]
      have hs : (-1 : R)^xs.length * (-1 : R)^xs.length = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc
        _ = ((-1 : R)^xs.length * (-1 : R)^xs.length) *
            gaussianOutputDeletion (B a) (gaussianInputPfaffian A B xs) ys := by rw [hs, one_mul]
        _ = _ := by ring
    rw [hrec]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact gaussianInputPfaffian_mem_listRowSpan A B (a :: xs)
    · apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (gaussianInputPfaffian_mem_listRowSpan A B _)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hx' hy'
    simpa only [map_add] using Submodule.add_mem _ hx' hy'
  · intro c x hx hx'
    simpa only [map_smul] using Submodule.smul_mem _ c hx'

/-- Every row for any other input block lies in the original ordered row span. -/
theorem gaussianInputPfaffian_mem_other_listRowSpan
    (A A' : Matrix I I R) (B : Matrix I J R) (xs : List I) :
    gaussianInputPfaffian A' B xs ∈ gaussianInputListRowSpan A B := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil =>
      have he : gaussianInputPfaffian A' B [] = gaussianInputPfaffian A B [] := by
        ext ys
        cases ys <;> simp
      rw [he]
      exact gaussianInputPfaffian_mem_listRowSpan A B []
    | cons a xs =>
      have he : gaussianInputPfaffian A' B (a :: xs) =
          (∑ j : Fin xs.length, ((-1 : R)^j.val * A' a xs[j]) •
            gaussianInputPfaffian A' B (xs.eraseIdx j.val)) +
          (-1 : R)^xs.length • gaussianOutputDeletion (B a) (gaussianInputPfaffian A' B xs) := by
        ext ys
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          gaussianInputPfaffian_cons]
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
        exact gaussianInputListRowSpan_deletion A B a _ (ih xs (by change xs.length < (a :: xs).length; simp))

/-- Changing the input-input block preserves the row space at the level of
ordered-list coefficients, proved directly from the Pfaffian recursion. -/
theorem gaussianInputListRowSpan_eq (A A' : Matrix I I R) (B : Matrix I J R) :
    gaussianInputListRowSpan A B = gaussianInputListRowSpan A' B := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨xs, rfl⟩
    exact gaussianInputPfaffian_mem_other_listRowSpan A' A B xs
  · rintro _ ⟨xs, rfl⟩
    exact gaussianInputPfaffian_mem_other_listRowSpan A A' B xs


/-- Skew input block gives a skew full Gaussian matrix. -/
theorem gaussianInputMatrix_skew (A : Matrix I I R) (B : Matrix I J R)
    (hA : ∀ i i', A i i' = -A i' i) (x y : I ⊕ J) :
    gaussianInputMatrix A B x y = -gaussianInputMatrix A B y x := by
  cases x <;> cases y
  · exact hA _ _
  · simp [gaussianInputMatrix]
  · rfl
  · simp [gaussianInputMatrix]

section Subsets

variable [LinearOrder I] [LinearOrder J]

/-- Actual subset-indexed Gaussian signature with input block A. Outputs are
reversed after increasing enumeration, exactly as in the planar cross chart. -/
def gaussianInputPlanarPfaffianMatrix (A : Matrix I I R) (B : Matrix I J R) :
    Matrix (Finset I) (Finset J) R :=
  fun s t => gaussianInputPfaffian A B (gaussianSubsetList s) (gaussianSubsetList t).reverse

@[simp] theorem gaussianInputPlanarPfaffianMatrix_zero (B : Matrix I J R) :
    gaussianInputPlanarPfaffianMatrix 0 B = gaussianPlanarPfaffianMatrix B := by
  ext s t
  simp [gaussianInputPlanarPfaffianMatrix, gaussianPlanarPfaffianMatrix]

/-- Evaluate output-list coefficients at the fixed planar subset orders. -/
def gaussianPlanarOutputEvaluation : (List J → R) →ₗ[R] (Finset J → R) where
  toFun F t := F (gaussianSubsetList t).reverse
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- All ordered input rows reduce to the true finite-subset row span. -/
theorem gaussianInputListRowSpan_evaluate [NoZeroDivisors R] [CharZero R]
    (A : Matrix I I R) (B : Matrix I J R) (hA : ∀ i i', A i i' = -A i' i)
    (F : List J → R) (hF : F ∈ gaussianInputListRowSpan A B) :
    gaussianPlanarOutputEvaluation F ∈
      Submodule.span R (Set.range (gaussianInputPlanarPfaffianMatrix A B).row) := by
  apply Submodule.span_induction (p := fun F _ =>
      gaussianPlanarOutputEvaluation F ∈
        Submodule.span R (Set.range (gaussianInputPlanarPfaffianMatrix A B).row))
      ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨xs, rfl⟩
    obtain ⟨c, hc⟩ := pfaffianList_input_normalization (gaussianInputMatrix A B)
      (gaussianInputMatrix_skew A B hA) xs
    have he : gaussianPlanarOutputEvaluation (gaussianInputPfaffian A B xs) =
        c • (gaussianInputPlanarPfaffianMatrix A B).row xs.toFinset := by
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
theorem gaussianInputPlanarPfaffianMatrix_rowSpan_eq [NoZeroDivisors R] [CharZero R]
    (A A' : Matrix I I R) (B : Matrix I J R)
    (hA : ∀ i i', A i i' = -A i' i) (hA' : ∀ i i', A' i i' = -A' i' i) :
    Submodule.span R (Set.range (gaussianInputPlanarPfaffianMatrix A B).row) =
      Submodule.span R (Set.range (gaussianInputPlanarPfaffianMatrix A' B).row) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨s, rfl⟩
    exact gaussianInputListRowSpan_evaluate A' B hA' _
      (gaussianInputPfaffian_mem_other_listRowSpan A' A B (gaussianSubsetList s))
  · rintro _ ⟨s, rfl⟩
    exact gaussianInputListRowSpan_evaluate A B hA _
      (gaussianInputPfaffian_mem_other_listRowSpan A A' B (gaussianSubsetList s))

/-- Input-quadratic elimination: the actual row span equals the cross-only
Pfaffian row span, in the same fixed planar output-reversal convention. -/
theorem gaussianInputPlanarPfaffianMatrix_rowSpan_eq_cross [NoZeroDivisors R] [CharZero R]
    (A : Matrix I I R) (B : Matrix I J R) (hA : ∀ i i', A i i' = -A i' i) :
    Submodule.span R (Set.range (gaussianInputPlanarPfaffianMatrix A B).row) =
      Submodule.span R (Set.range (gaussianPlanarPfaffianMatrix B).row) := by
  simpa only [gaussianInputPlanarPfaffianMatrix_zero] using
    gaussianInputPlanarPfaffianMatrix_rowSpan_eq A 0 B hA (by simp)

end Subsets

section Rank

variable {K : Type*} [Field K] [CharZero K] [Fintype I] [Fintype J]
  [LinearOrder I] [LinearOrder J]

/-- Rank formula for the actual Gaussian Pfaffian matrix with an arbitrary skew
input quadratic block and zero output quadratic block. -/
theorem gaussianInputPlanarPfaffianMatrix_rank (A : Matrix I I K) (B : Matrix I J K)
    (hA : ∀ i i', A i i' = -A i' i) :
    (gaussianInputPlanarPfaffianMatrix A B).rank = 2 ^ B.rank := by
  rw [Matrix.rank_eq_finrank_span_row,
    gaussianInputPlanarPfaffianMatrix_rowSpan_eq_cross A B hA,
    ← Matrix.rank_eq_finrank_span_row, gaussianPlanarPfaffianMatrix_rank]

/-- Rank two forces a rank-one cross block even in the presence of any input
quadratic block. -/
theorem gaussianInputPlanarPfaffianMatrix_rank_two_iff
    (A : Matrix I I K) (B : Matrix I J K) (hA : ∀ i i', A i i' = -A i' i) :
    (gaussianInputPlanarPfaffianMatrix A B).rank = 2 ↔ B.rank = 1 := by
  rw [gaussianInputPlanarPfaffianMatrix_rank A B hA]
  change 2 ^ B.rank = 2 ^ 1 ↔ B.rank = 1
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff

end Rank

end
end MatchgateWidth
