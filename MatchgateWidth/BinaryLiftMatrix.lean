import MatchgateWidth.BinaryContextMatrixSupport

/-! # Literal binary Boolean lift and its preserved rank -/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

def binaryMatrixLift {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (BooleanInput t) (BooleanInput t) ℂ :=
  M.transpose*A*M

@[simp] theorem binaryMatrixLift_transpose {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    (binaryMatrixLift M A).transpose = binaryMatrixLift M A.transpose := by
  simp [binaryMatrixLift,Matrix.transpose_mul,Matrix.mul_assoc]

theorem binaryMatrixLift_recover {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (N : Matrix (BooleanInput t) (Fin 3) ℂ) (hN : M*N=1) :
    N.transpose*binaryMatrixLift M A*N=A := by
  have hNt : N.transpose*M.transpose=1 := by rw [← Matrix.transpose_mul,hN,Matrix.transpose_one]
  simp only [binaryMatrixLift,← Matrix.mul_assoc,hNt,Matrix.one_mul]
  rw [Matrix.mul_assoc,hN,Matrix.mul_one]

theorem binaryMatrixLift_rank {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) : (binaryMatrixLift M A).rank=A.rank := by
  obtain ⟨N,hN⟩ := exists_baseDecoder M (transpose_injective_of_rank_eq_card M (by simpa using hM))
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left (M.transpose*A) M).trans
      (Matrix.rank_mul_le_right M.transpose A)
  · have hl := (Matrix.rank_mul_le_left (N.transpose*binaryMatrixLift M A) N).trans
      (Matrix.rank_mul_le_right N.transpose (binaryMatrixLift M A))
    rwa [binaryMatrixLift_recover M A N hN] at hl

theorem span_rows_mul_le {I J K : Type*} [Fintype J]
    (C : Matrix I J ℂ) (D : Matrix J K ℂ) :
    Submodule.span ℂ (Set.range (C*D).row) ≤ Submodule.span ℂ (Set.range D.row) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have he : (C*D).row i = ∑ j, C i j • D.row j := by
    ext k
    simp [Matrix.mul_apply]
  rw [he]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

theorem binaryMatrixLift_rowspace {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    orderedRowSpace (binaryMatrixLift M A) =
      (Submodule.span ℂ (Set.range A.row)).map M.transpose.mulVecLin := by
  rw [span_rows_map_transpose]
  obtain ⟨N,hN⟩ := exists_baseDecoder M (transpose_injective_of_rank_eq_card M (by simpa using hM))
  have hNt : N.transpose*M.transpose=1 := by rw [← Matrix.transpose_mul,hN,Matrix.transpose_one]
  have he : N.transpose*binaryMatrixLift M A=A*M := by
    simp only [binaryMatrixLift,← Matrix.mul_assoc,hNt,Matrix.one_mul]
  apply le_antisymm
  · simpa only [binaryMatrixLift,Matrix.mul_assoc,orderedRowSpace] using span_rows_mul_le M.transpose (A*M)
  · rw [← he]
    exact span_rows_mul_le N.transpose (binaryMatrixLift M A)

theorem binaryMatrixLift_rowspace_le {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    orderedRowSpace (binaryMatrixLift M A) ≤ Submodule.span ℂ (Set.range M.row) :=
  span_rows_mul_le (M.transpose*A) M

/-- Power-of-two rank is proved from the actual Gaussian chart. -/
theorem OrderedMatchgateMatrix.rank_zero_or_power {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (hP : OrderedMatchgateMatrix P) :
    P.rank=0 ∨ ∃ k, P.rank=2^k := by
  obtain ⟨p,q,c,A,B,D,hA,hD,_,_,he⟩ := hP.exists_gaussian_chart
  have hPeq : P = c • (gaussianOrderedMatrix A B D).submatrix
      (booleanXorEquiv p) (booleanXorEquiv q) := by ext x y; exact he x y
  by_cases hc : c=0
  · left; simp [hPeq,hc]
  · right
    refine ⟨B.rank,?_⟩
    rw [hPeq,rank_scaled_xor _ p q hc,gaussianOrderedMatrix_rank _ _ _ hA hD]

 theorem binaryMatrixLift_rank_cases {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : ExactMatchgateMatrix (binaryMatrixLift M A)) :
    A.rank=0 ∨ A.rank=1 ∨ A.rank=2 := by
  have hle : A.rank ≤ 3 := by simpa using Matrix.rank_le_card_width A
  rcases hA.identities.rank_zero_or_power with hz | ⟨k,hk⟩
  · exact Or.inl ((binaryMatrixLift_rank M hM A).symm.trans hz)
  · rw [binaryMatrixLift_rank M hM A] at hk
    have hk2 : k ≤ 1 := by
      by_contra hn
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ k by omega)
      rw [← hk] at hh
      norm_num at hh
      omega
    have hh : k=0 ∨ k=1 := by omega
    rcases hh with rfl | rfl
    · exact Or.inr (Or.inl (by simpa using hk))
    · exact Or.inr (Or.inr (by simpa using hk))

end
end MatchgateWidth
