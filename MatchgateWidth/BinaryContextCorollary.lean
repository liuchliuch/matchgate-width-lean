import MatchgateWidth.BinaryContextAdaptedBasis

/-! # Source Corollary 10.10 for actual boundary tensors
Every boundary tensor is represented in the same fixed adapted basis and its
inverse. The matrix is derived from its literal coefficients. This statement
applies to every exact lifted two-port tensor, hence to every valid binary
context once the generic gadget exact-lifting theorem is applied.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

/-- Actual coefficient matrix after the inverse fixed basis transformation. -/
def binaryContextCoordinates (N : Matrix (Fin 3) (Fin 3) ℂ)
    (F : (Fin 2 → Fin 3) → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => leftTransform N F ![i,j]

theorem binaryDomainTensor_coordinates (N : Matrix (Fin 3) (Fin 3) ℂ)
    (F : (Fin 2 → Fin 3) → ℂ) :
    binaryDomainTensor (binaryContextCoordinates N F)=leftTransform N F := by
  funext x
  unfold binaryDomainTensor binaryContextCoordinates
  congr 1
  ext i
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem binaryContextCoordinates_reconstruct
    (T N : Matrix (Fin 3) (Fin 3) ℂ) (hNT : N*T=1)
    (F : (Fin 2 → Fin 3) → ℂ) :
    leftTransform T (binaryDomainTensor (binaryContextCoordinates N F))=F := by
  rw [binaryDomainTensor_coordinates,leftTransform_compose,hNT,
    leftTransform_eq_tensorPowerMatrix_transpose_mulVecLin]
  have hp : tensorPowerMatrix (P := Fin 2) (1 : Matrix (Fin 3) (Fin 3) ℂ) =
      (1 : Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ) := by
    classical
    ext x y
    change (∏ i : Fin 2, (1 : Matrix (Fin 3) (Fin 3) ℂ) (x i) (y i)) = _
    by_cases hxy : x=y
    · subst y
      simp
    · have hi : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
      obtain ⟨i,hi⟩ := hi
      have hz : (∏ j : Fin 2, (1 : Matrix (Fin 3) (Fin 3) ℂ) (x j) (y j))=0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simpa [hxy] using hz
  rw [hp]
  simp

/-- Fixed-basis form for every actual binary boundary tensor, without any
assumption that its coordinates are already monomial or plane-confined. -/
theorem binary_context_alternative_for_tensors {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (T N : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3) (hNT : N*T=1)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows (T*M) Q) :
    BinarySmallCover M ∨ ∀ F : (Fin 2 → Fin 3) → ℂ,
      ExactMatchgate (leftBooleanLift M 2 F) → PartialMonomial (binaryContextCoordinates N F) := by
  rcases exact_binary_context_alternative_fixed_basis M hM T hT Q d with hc | hm
  · exact Or.inl hc
  · right
    intro F hF
    apply hm
    rwa [binaryContextCoordinates_reconstruct T N hNT]

/-- The full binary-context alternative from the literal realized plane and
transverse pure ray. One adapted basis and inverse are selected once, with
canonical parity endpoint lines, before all binary contexts are quantified. -/
theorem binary_context_corollary {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (P : Submodule ℂ (Fin 3 → ℂ))
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hrB : B.rank=2)
    (hspace : orderedRowSpace B=P.map M.transpose.mulVecLin)
    (r : Fin 3 → ℂ) (hrP : r ∉ P) (hr : ExactMatchgate (unaryTransform M r)) :
    ∃ T N : Matrix (Fin 3) (Fin 3) ℂ,
      T.rank=3 ∧ T*N=1 ∧ N*T=1 ∧ T.row 2=r ∧
      primitiveParityEndpoint M P 0=Submodule.span ℂ {T.row 0} ∧
      primitiveParityEndpoint M P 1=Submodule.span ℂ {T.row 1} ∧
      (BinarySmallCover M ∨ ∀ F : (Fin 2 → Fin 3) → ℂ,
        ExactMatchgate (leftBooleanLift M 2 F) → PartialMonomial (binaryContextCoordinates N F)) := by
  obtain ⟨T,Q,hT,hTr,he0,he1,d⟩ := exists_binary_adapted_basis M hM P B hB hrB hspace r hrP hr
  obtain ⟨N,hTN⟩ := exists_baseDecoder T (transpose_injective_of_rank_eq_card T (by simpa using hT))
  have hNT : N*T=1 := mul_eq_one_comm.mp hTN
  exact ⟨T,N,hT,hTN,hNT,hTr,he0,he1,binary_context_alternative_for_tensors M hM T N hT hNT Q d⟩

/-- The source's consequence for an actual binary context of the original
presentation: exact labelled width at most three with all labels retained. -/
theorem LabelledCommonPresentation.binary_context_forces_width_three
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank=3)
    (T N : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.rank=3) (hNT : N*T=1)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows (T*p.baseMatrix) Q)
    (F : (Fin 2 → Fin 3) → ℂ) (hF : ExactMatchgate (leftBooleanLift p.baseMatrix 2 F))
    (hn : ¬ PartialMonomial (binaryContextCoordinates N F)) :
    ∃ r ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) r,
      q.left=p.left ∧ q.language=p.language ∧ ExactlyLabelledEquivalent p.language q.language := by
  apply p.binary_nonmonomial_fixed_basis_compression hM T hT Q d (binaryContextCoordinates N F) _ hn
  rwa [binaryContextCoordinates_reconstruct T N hNT]

/-- Both the alternatives and the width-three consequence for one original
labelled presentation, with the same fixed coefficient map in both clauses. -/
theorem LabelledCommonPresentation.binary_context_corollary
    {S : LabelledShape} {s t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank=3) (P : Submodule ℂ (Fin 3 → ℂ))
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hrB : B.rank=2)
    (hspace : orderedRowSpace B=P.map p.baseMatrix.transpose.mulVecLin)
    (r : Fin 3 → ℂ) (hrP : r ∉ P) (hr : ExactMatchgate (unaryTransform p.baseMatrix r)) :
    ∃ T N : Matrix (Fin 3) (Fin 3) ℂ,
      T.rank=3 ∧ T*N=1 ∧ N*T=1 ∧ T.row 2=r ∧
      primitiveParityEndpoint p.baseMatrix P 0=Submodule.span ℂ {T.row 0} ∧
      primitiveParityEndpoint p.baseMatrix P 1=Submodule.span ℂ {T.row 1} ∧
      (BinarySmallCover p.baseMatrix ∨ ∀ F : (Fin 2 → Fin 3) → ℂ,
        ExactMatchgate (leftBooleanLift p.baseMatrix 2 F) → PartialMonomial (binaryContextCoordinates N F)) ∧
      (∀ F : (Fin 2 → Fin 3) → ℂ, ExactMatchgate (leftBooleanLift p.baseMatrix 2 F) →
        ¬ PartialMonomial (binaryContextCoordinates N F) →
        ∃ w ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) w,
          q.left=p.left ∧ q.language=p.language ∧ ExactlyLabelledEquivalent p.language q.language) := by
  obtain ⟨T,Q,hT,hTr,he0,he1,d⟩ :=
    exists_binary_adapted_basis p.baseMatrix hM P B hB hrB hspace r hrP hr
  obtain ⟨N,hTN⟩ := exists_baseDecoder T (transpose_injective_of_rank_eq_card T (by simpa using hT))
  have hNT : N*T=1 := mul_eq_one_comm.mp hTN
  refine ⟨T,N,hT,hTN,hNT,hTr,he0,he1,
    binary_context_alternative_for_tensors p.baseMatrix hM T N hT hNT Q d,?_⟩
  intro F hF hn
  exact p.binary_context_forces_width_three hM T N hT hNT Q d F hF hn

end
end MatchgateWidth
