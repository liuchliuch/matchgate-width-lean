import MatchgateWidth.BinaryPhysicalContext

/-! # Original presentation and fixed adapted coordinate data
The basis change is fixed before the binary tensor. Covers are returned for the
original base; compression preserves all original labels and their language.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

theorem span_rows_fullrank_basis_change {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3) :
    Submodule.span ℂ (Set.range (T*M).row)=Submodule.span ℂ (Set.range M.row) := by
  obtain ⟨N,hN⟩ := exists_baseDecoder T (transpose_injective_of_rank_eq_card T (by simpa using hT))
  have hNt : N*T=1 := mul_eq_one_comm.mp hN
  have he : N*(T*M)=M := by rw [← Matrix.mul_assoc,hNt,Matrix.one_mul]
  apply le_antisymm (span_rows_mul_le T M)
  calc
    _ = Submodule.span ℂ (Set.range (N*(T*M)).row) := congrArg (fun B => Submodule.span ℂ (Set.range B.row)) he.symm
    _ ≤ _ := span_rows_mul_le N (T*M)

theorem rank_fullrank_basis_change {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3) : (T*M).rank=M.rank := by
  rw [Matrix.rank_eq_finrank_span_row,span_rows_fullrank_basis_change M T hT,
    ← Matrix.rank_eq_finrank_span_row]

theorem binarySmallCover_basis_change_iff {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3) :
    BinarySmallCover (T*M) ↔ BinarySmallCover M := by
  simp only [BinarySmallCover,span_rows_fullrank_basis_change M T hT]

 theorem leftBooleanLift_basis_change_binary {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    leftBooleanLift M 2 (leftTransform T (binaryDomainTensor A)) =
      leftBooleanLift (T*M) 2 (binaryDomainTensor A) := by
  funext z
  unfold leftBooleanLift
  rw [leftTransform_compose]

/-- Corollary 10.10 in fixed adapted coordinates of the original base. -/
theorem exact_binary_context_alternative_fixed_basis {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows (T*M) Q) :
    BinarySmallCover M ∨ ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      ExactMatchgate (leftBooleanLift M 2 (leftTransform T (binaryDomainTensor A))) →
      PartialMonomial A := by
  rcases exact_binary_context_alternative (T*M)
    ((rank_fullrank_basis_change M T hT).trans hM) Q d with hc | hm
  · exact Or.inl ((binarySmallCover_basis_change_iff M T hT).mp hc)
  · right
    intro A hA
    apply hm A
    rwa [leftBooleanLift_basis_change_binary] at hA

/-- One actual nonmonomial boundary context compresses the original labelled
presentation to width at most three, even if the adapted basis is nontrivial. -/
theorem LabelledCommonPresentation.binary_nonmonomial_fixed_basis_compression
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank=3)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows (T*p.baseMatrix) Q)
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ExactMatchgate (leftBooleanLift p.baseMatrix 2 (leftTransform T (binaryDomainTensor A))))
    (hn : ¬ PartialMonomial A) :
    ∃ r ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) r,
      q.left=p.left ∧ q.language=p.language ∧ ExactlyLabelledEquivalent p.language q.language := by
  have hc : BinarySmallCover p.baseMatrix := by
    rcases exact_binary_context_alternative_fixed_basis p.baseMatrix hM T hT Q d with hc | hm
    · exact hc
    · exact (hn (hm A hA)).elim
  rcases hc with ⟨H,hH,hr,hcover⟩ | ⟨H,hH,hr,hcover⟩
  · obtain ⟨q,_,hl,he,heq⟩ := p.exists_exactly_equivalent_of_common_cover H hH hr hcover
    exact ⟨2,by decide,q,hl,he,heq⟩
  · obtain ⟨q,_,hl,he,heq⟩ := p.exists_exactly_equivalent_of_common_cover H hH hr hcover
    exact ⟨3,by decide,q,hl,he,heq⟩

end
end MatchgateWidth
