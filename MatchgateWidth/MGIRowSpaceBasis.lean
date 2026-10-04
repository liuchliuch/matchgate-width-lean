import MatchgateWidth.RankTwoGaussianHull
import MatchgateWidth.MGIMatrixTranspose

/-! # Full-row ordered covers of arbitrary MGI row spaces
A rank-`2^r` ordered MGI matrix has an actual `r`-input ordered MGI submatrix
with the same row space. The row selection is a pinned Boolean mode cube,
obtained constructively from a Gaussian chart and an increasing cross-row basis.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] {r m t : ℕ}

/-- Every matrix has an increasing set of basis rows of size exactly its rank. -/
theorem exists_increasing_rank_row_basis (B : Matrix (Fin m) (Fin t) K)
    (hB : B.rank = r) : ∃ e : Fin r ↪o Fin m, (B.submatrix e id).rank = r := by
  classical
  obtain ⟨s, _, _, hs, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K B.row) (Set.empty_subset (Set.univ : Set (Fin m)))
  have hspan : Submodule.span K (B.row '' s) = Submodule.span K (Set.range B.row) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro v ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      simpa only [Set.image_univ] using hs
  have hrange : Set.range (fun i : s => B.row i) = B.row '' s := by ext v; simp
  let : Fintype s := Fintype.ofFinite s
  have hc : Fintype.card s = r := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Fintype.card s = Module.finrank K (Submodule.span K (Set.range (fun i : s => B.row i))) at h
    rwa [hrange, hspan, ← Matrix.rank_eq_finrank_span_row, hB] at h
  let sf := s.toFinset
  have hsf : sf.card = r := by simpa only [sf, Set.toFinset_card] using hc
  let e : Fin r ↪o Fin m := sf.orderEmbOfFin hsf
  refine ⟨e, ?_⟩
  rw [Matrix.rank_eq_finrank_span_row]
  have hr : Set.range (B.submatrix e id).row = B.row '' s := by
    change Set.range (B.row ∘ e) = _
    rw [Set.range_comp, show Set.range e = s from by
      simpa only [e, sf, Set.coe_toFinset] using sf.range_orderEmbOfFin hsf]
  rw [hr, hspan, ← Matrix.rank_eq_finrank_span_row, hB]

variable {R : Type*} [CommRing R]

/-- Literal increasing input-mode restriction, all other inputs pinned to zero. -/
def inputModeRestriction (P : Matrix (BooleanInput m) (BooleanInput t) R)
    (e : Fin r ↪o Fin m) : Matrix (BooleanInput r) (BooleanInput t) R :=
  (pinnedOutputMatrix P.transpose (reverseOutputEmbedding e).toEmbedding ∅).transpose

@[simp] theorem inputModeRestriction_apply
    (P : Matrix (BooleanInput m) (BooleanInput t) R) (e : Fin r ↪o Fin m)
    (x : BooleanInput r) (y : BooleanInput t) :
    inputModeRestriction P e x y =
      P ((booleanSubsetEquiv m).symm (((booleanSubsetEquiv r) x).map e.toEmbedding)) y := by
  simp [inputModeRestriction, pinnedOutputMatrix]

/-- Input-mode restriction preserves exact ordered MGI. -/
theorem OrderedMatchgateMatrix.inputModeRestriction
    {P : Matrix (BooleanInput m) (BooleanInput t) R} (hP : OrderedMatchgateMatrix P)
    (e : Fin r ↪o Fin m) : OrderedMatchgateMatrix (inputModeRestriction P e) :=
  (hP.transpose.pinnedOutput (reverseOutputEmbedding e).toEmbedding
    (reverseOutputEmbedding e).strictMono ∅).transpose

/-- Gaussian transposition with all signs fixed by the physical boundary order. -/
theorem gaussianOrderedMatrix_transpose (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin m) (Fin t) R) (D : Matrix (Fin t) (Fin t) R)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i) :
    (gaussianOrderedMatrix A B D).transpose = gaussianOrderedMatrix (-D) B.transpose (-A) := by
  unfold gaussianOrderedMatrix
  rw [Matrix.transpose_submatrix, gaussianFullPlanarPfaffianMatrix_transpose A B D hA hD]

/-- Restriction keeps both quadratic blocks and restricts the true cross matrix. -/
theorem gaussianOrderedMatrix_inputModeRestriction (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin m) (Fin t) R) (D : Matrix (Fin t) (Fin t) R)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i)
    (e : Fin r ↪o Fin m) :
    inputModeRestriction (gaussianOrderedMatrix A B D) e =
      gaussianOrderedMatrix (A.submatrix e e) (B.submatrix e id) D := by
  unfold inputModeRestriction
  rw [gaussianOrderedMatrix_transpose A B D hA hD, gaussianOrderedMatrix_pinnedOutput]
  rw [gaussianOrderedMatrix_transpose]
  · congr 1 <;> ext i j <;> simp
  · intro i j; simpa using congrArg Neg.neg (hD i j)
  · intro i j; simpa using congrArg Neg.neg (hA (e i) (e j))

variable [CharZero K]

/-- Any nonzero-rank ordered MGI row space admits a full-row MGI basis
using precisely the logarithm of its rank in Boolean input modes. -/
theorem OrderedMatchgateMatrix.exists_fullRow_cover
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2 ^ r) :
    ∃ Q : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix Q ∧ Q.rank = 2 ^ r ∧ orderedRowSpace Q = orderedRowSpace P := by
  obtain ⟨p, q, c, A, B, D, hA, hD, _, _, heq⟩ := hP.exists_gaussian_chart
  have hPeq : P = c • (gaussianOrderedMatrix A B D).submatrix
      (booleanXorEquiv p) (booleanXorEquiv q) := by
    ext x y; exact heq x y
  have hc : c ≠ 0 := by
    intro hz
    rw [hPeq, hz, zero_smul, Matrix.rank_zero] at hPr
    exact (Nat.ne_of_gt (Nat.two_pow_pos r)) hPr.symm
  have hBr : B.rank = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    rw [hPeq, rank_scaled_xor _ p q hc, gaussianOrderedMatrix_rank _ _ _ hA hD] at hPr
    exact hPr
  obtain ⟨e, he⟩ := exists_increasing_rank_row_basis B hBr
  let Q : Matrix (BooleanInput r) (BooleanInput t) K :=
    MatchgateWidth.inputModeRestriction (fun (x : BooleanInput m) y => P (pfaffianXor p x) y) e
  have hQ : OrderedMatchgateMatrix Q := (hP.inputXor p).inputModeRestriction e
  have hQeq : Q = c • (gaussianOrderedMatrix (A.submatrix e e) (B.submatrix e id) D).submatrix
      (Equiv.refl _) (booleanXorEquiv q) := by
    ext x y
    change P (pfaffianXor p _) y = _
    rw [heq]
    simp only [pfaffianXor_involutive,   
       booleanXorEquiv]
    rw [← gaussianOrderedMatrix_inputModeRestriction A B D hA hD e]
    rfl
  have hAr : ∀ i j, (A.submatrix e e) i j = -(A.submatrix e e) j i := fun i j => hA (e i) (e j)
  have hQr : Q.rank = 2 ^ r := by
    rw [hQeq, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc),
      Matrix.rank_submatrix, gaussianOrderedMatrix_rank _ _ _ hAr hD, he]
  refine ⟨Q, hQ, hQr, ?_⟩
  have hle : orderedRowSpace Q ≤ orderedRowSpace P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hrow : Q.row x = P.row
        (pfaffianXor p ((booleanSubsetEquiv m).symm (((booleanSubsetEquiv r) x).map e.toEmbedding))) := by
      funext y
      exact inputModeRestriction_apply (fun (x : BooleanInput m) y => P (pfaffianXor p x) y) e x y
    rw [hrow]
    exact row_mem_orderedRowSpace P _
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [orderedRowSpace, orderedRowSpace, ← Matrix.rank_eq_finrank_span_row,
    ← Matrix.rank_eq_finrank_span_row, hPr, hQr]

end
end MatchgateWidth
