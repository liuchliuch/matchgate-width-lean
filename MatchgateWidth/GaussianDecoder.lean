import MatchgateWidth.GaussianPinnedMinor
import MatchgateWidth.GaussianOrderedMatrix

/-! # Genuine ordered decoders for full-row-rank Gaussian matrices -/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff

/-- An increasing embedding of logical output modes, conjugated into the
reversed physical boundary order. -/
def reverseOutputEmbedding {r t : ℕ} (e : Fin r ↪o Fin t) : Fin r ↪o Fin t :=
  OrderEmbedding.ofStrictMono (fun i => (e i.rev).rev) (by
    intro i j h
    exact Fin.rev_lt_rev.mpr (e.strictMono (Fin.rev_lt_rev.mpr h)))

@[simp] theorem reverseOutputEmbedding_apply {r t : ℕ}
    (e : Fin r ↪o Fin t) (i : Fin r) : reverseOutputEmbedding e i = (e i.rev).rev := rfl

@[simp] theorem reversePortSubset_map_reverseOutputEmbedding {r t : ℕ}
    (e : Fin r ↪o Fin t) (S : Finset (Fin r)) :
    reversePortSubset ((reversePortSubset S).map (reverseOutputEmbedding e).toEmbedding) =
      S.map e.toEmbedding := by
  ext i
  simp only [mem_reversePortSubset, Finset.mem_map, mem_reversePortSubset]
  constructor
  · rintro ⟨j, hj, he⟩
    refine ⟨j.rev, hj, ?_⟩
    change (e j.rev).rev = i.rev at he
    exact Fin.rev_injective he
  · rintro ⟨j, hj, he⟩
    refine ⟨j.rev, by simpa using hj, ?_⟩
    change (e j.rev.rev).rev = i.rev
    simpa only [Fin.rev_rev, RelEmbedding.coe_toEmbedding] using congrArg Fin.rev he

@[simp] theorem pinnedOutputWord_reverseOutputEmbedding {r t : ℕ}
    (e : Fin r ↪o Fin t) (x : BooleanInput r) :
    pinnedOutputWord (reverseOutputEmbedding e).toEmbedding ∅ x =
      (booleanSubsetEquiv t).symm (((booleanSubsetEquiv r) x).map e.toEmbedding) := by
  simp only [pinnedOutputWord, show ∀ S : Finset (Fin t), S ∆ ∅ = S from symmDiff_bot,
    reversePortSubset_map_reverseOutputEmbedding]

variable {R : Type*} [CommRing R]

/-- The exact ordered pinning construction selects precisely the increasing
Gaussian output-mode cube, despite the reversed physical output convention. -/
theorem gaussianOrderedMatrix_pinnedOutput {r t s : ℕ}
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin r) (Fin t) R)
    (D : Matrix (Fin t) (Fin t) R) (e : Fin s ↪o Fin t) :
    pinnedOutputMatrix (gaussianOrderedMatrix A B D)
      (reverseOutputEmbedding e).toEmbedding ∅ =
      gaussianOrderedMatrix A (B.submatrix id e) (D.submatrix e e) := by
  ext x y
  simp only [pinnedOutputMatrix, Matrix.submatrix_apply,
    pinnedOutputWord_reverseOutputEmbedding, id_eq, gaussianOrderedMatrix,
    Equiv.apply_symm_apply]
  exact congrFun (congrFun (gaussianFullPlanarPfaffianMatrix_map_output A B D e)
    ((booleanSubsetEquiv r) x)) ((booleanSubsetEquiv s) y)

variable {K : Type*} [Field K] [CharZero K]

/-- Skew matrices over characteristic-zero fields have zero diagonal. -/
theorem skew_diagonal_eq_zero {ι : Type*} (A : Matrix ι ι K)
    (hA : ∀ i j, A i j = -A j i) (i : ι) : A i i = 0 := by
  have h := hA i i
  have htwo : (2 : K) * A i i = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Every full-row-rank full Gaussian matrix has a right inverse in the literal
ordered MGI class, with both quadratic blocks arbitrary. -/
theorem gaussianOrderedMatrix_exists_rightInverse {r t : ℕ}
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i)
    (hfull : (gaussianOrderedMatrix A B D).rank = 2 ^ r) :
    ∃ N : Matrix (BooleanInput t) (BooleanInput r) K,
      OrderedMatchgateMatrix N ∧ gaussianOrderedMatrix A B D * N = 1 := by
  have hB : B.rank = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    rwa [gaussianOrderedMatrix_rank A B D hA hD] at hfull
  obtain ⟨e, he⟩ := exists_increasing_fullRank_column_minor B hB
  have hP := gaussianOrderedMatrix_isMatchgate A B D hA hD
    (skew_diagonal_eq_zero A hA) (skew_diagonal_eq_zero D hD)
  apply hP.exists_rightInverse_of_pinned_det (reverseOutputEmbedding e).toEmbedding
    (reverseOutputEmbedding e).strictMono ∅
  rw [gaussianOrderedMatrix_pinnedOutput]
  let Q := gaussianOrderedMatrix A (B.submatrix id e) (D.submatrix e e)
  have hQ : Q.rank = Fintype.card (BooleanInput r) := by
    dsimp only [Q]
    rw [gaussianOrderedMatrix_rank A (B.submatrix id e) (D.submatrix e e) hA
      (fun i j => hD (e i) (e j)), he]
    simp [BooleanInput]
  obtain ⟨N, hN⟩ := exists_baseDecoder Q (transpose_injective_of_rank_eq_card Q hQ)
  exact Matrix.isUnit_det_of_right_inverse hN

end
end MatchgateWidth
