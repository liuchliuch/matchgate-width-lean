import MatchgateWidth.BinaryContextParity

/-! # The binary-context alternative in one fixed adapted ray basis
The same base and endpoint encoder are fixed before the context matrix is
quantified. The rank-one pure-ray and rank-two plane arguments are derived
from each exact lift; no monomiality or cover conclusion is assumed.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

 theorem matrix_eq_zero_of_rank_zero (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hr : A.rank=0) : A=0 := by
  have hs : Submodule.span ℂ (Set.range A.row) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rwa [← Matrix.rank_eq_finrank_span_row]
  ext i j
  have hi : A.row i ∈ Submodule.span ℂ (Set.range A.row) := Submodule.subset_span ⟨i,rfl⟩
  rw [hs,Submodule.mem_bot] at hi
  exact congrFun hi j

 theorem BinaryAdaptedRows.binary_partial_monomial_of_no_cover {t : ℕ}
    {M : Matrix (Fin 3) (BooleanInput t) ℂ}
    {Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ}
    (d : BinaryAdaptedRows M Q) (hM : M.rank=3) (hno : ¬ BinarySmallCover M)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : ExactMatchgateMatrix (binaryMatrixLift M A)) :
    PartialMonomial A := by
  have hAt : ExactMatchgateMatrix (binaryMatrixLift M A.transpose) := by
    simpa only [binaryMatrixLift_transpose] using hA.transpose
  rcases binaryMatrixLift_rank_cases M hM A hA with hz | h1 | h2
  · rw [matrix_eq_zero_of_rank_zero A hz]
    exact partialMonomial_zero
  · obtain ⟨j,hj⟩ := d.rank_one_space_coordinate hM hno (binaryMatrixLift M A) hA
      (by rw [binaryMatrixLift_rank M hM A,h1]) (binaryMatrixLift_rowspace_le M A)
    obtain ⟨i,hi⟩ := d.rank_one_space_coordinate hM hno (binaryMatrixLift M A.transpose) hAt
      (by rw [binaryMatrixLift_rank M hM A.transpose,Matrix.rank_transpose,h1])
      (binaryMatrixLift_rowspace_le M A.transpose)
    rw [binaryMatrixLift_rowspace M hM A] at hj
    rw [binaryMatrixLift_rowspace M hM A.transpose] at hi
    apply partialMonomial_of_single_coordinate A i j
    · exact matrix_rows_zero_of_image_coordinate M hM A j hj
    · intro a b ha
      exact matrix_rows_zero_of_image_coordinate M hM A.transpose i hi b a ha
  · have hs := d.rank_two_space_eq hM hno (binaryMatrixLift M A) hA
      (by rw [binaryMatrixLift_rank M hM A,h2]) (binaryMatrixLift_rowspace_le M A)
    have hst := d.rank_two_space_eq hM hno (binaryMatrixLift M A.transpose) hAt
      (by rw [binaryMatrixLift_rank M hM A.transpose,Matrix.rank_transpose,h2])
      (binaryMatrixLift_rowspace_le M A.transpose)
    rw [binaryMatrixLift_rowspace M hM A,d.plane_space] at hs
    rw [binaryMatrixLift_rowspace M hM A.transpose,d.plane_space] at hst
    exact d.plane_binary_partial_monomial hM A hA
      (matrix_rows_zero_third_of_image_plane M hM A hs.le)
      (matrix_rows_zero_third_of_image_plane M hM A.transpose hst.le)

/-- Source Corollary 10.10's alternatives for exact binary matrices, in one
fixed adapted basis, uniformly for every binary context. -/
theorem binary_context_alternative {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows M Q) :
    BinarySmallCover M ∨ ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      ExactMatchgateMatrix (binaryMatrixLift M A) → PartialMonomial A := by
  by_cases hc : BinarySmallCover M
  · exact Or.inl hc
  · exact Or.inr (d.binary_partial_monomial_of_no_cover hM hc)

/-- One non-partial-monomial context forces an actual rank-four or rank-eight
common exact cover, not merely an abstract numerical width bound. -/
theorem binary_nonmonomial_forces_cover {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows M Q)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : ExactMatchgateMatrix (binaryMatrixLift M A))
    (hn : ¬ PartialMonomial A) : BinarySmallCover M := by
  rcases binary_context_alternative M hM Q d with hc | hm
  · exact hc
  · exact (hn (hm A hA)).elim

/-- The concluding width bound constructs a presentation with the very same
label types, domain and induced language. -/
theorem LabelledCommonPresentation.binary_nonmonomial_compression
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank=3)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows p.baseMatrix Q)
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ExactMatchgateMatrix (binaryMatrixLift p.baseMatrix A)) (hn : ¬ PartialMonomial A) :
    ∃ r ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) r,
      q.left=p.left ∧ q.language=p.language ∧ ExactlyLabelledEquivalent p.language q.language := by
  rcases binary_nonmonomial_forces_cover p.baseMatrix hM Q d A hA hn with hc | hc
  · obtain ⟨H,hH,hr,hcover⟩ := hc
    obtain ⟨q,_,hl,he,heq⟩ := p.exists_exactly_equivalent_of_common_cover H hH hr hcover
    exact ⟨2,by decide,q,hl,he,heq⟩
  · obtain ⟨H,hH,hr,hcover⟩ := hc
    obtain ⟨q,_,hl,he,heq⟩ := p.exists_exactly_equivalent_of_common_cover H hH hr hcover
    exact ⟨3,by decide,q,hl,he,heq⟩

end
end MatchgateWidth
