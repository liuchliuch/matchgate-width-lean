import MatchgateWidth.ExactMatchgateBounds
import MatchgateWidth.CoverCompressionAlgebra
import MatchgateWidth.CliffordPinRealization

/-! # Exact geometric transpose, Pin realization, hull, decoder and compression -/
namespace MatchgateWidth
noncomputable section

/-- Exact matrices use the prescribed increasing-input/reversed-output order. -/
def ExactMatchgateMatrix {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) ℂ) : Prop :=
  ExactMatchgate (orderedMatrixSignature P)

theorem ExactMatchgateMatrix.identities {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (hP : ExactMatchgateMatrix P) :
    OrderedMatchgateMatrix P := ExactMatchgate.matchgateIdentities hP

theorem OrderedMatchgateMatrix.exactMatrix {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (hP : OrderedMatchgateMatrix P) :
    ExactMatchgateMatrix P := BooleanMatchgateIdentities.exactMatchgate hP

/-- Lemma4.3(a): ordinary transpose, not Hermitian adjoint. -/
theorem ExactMatchgateMatrix.transpose {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (hP : ExactMatchgateMatrix P) :
    ExactMatchgateMatrix P.transpose := hP.identities.transpose.exactMatrix

/-- Lemma4.3(b) in the actual universal Clifford/Pin representation. The matrix
is the standard COLUMN coefficient matrix, with optional nonzero normalization
scalar; both it and its true inverse are exact ordered matchgate matrices. -/
theorem pin_lift_exact_coefficient_matrices {t : ℕ}
    (x : pinGroup (splitCliffordQuadratic (K := ℂ) (t := t)))
    (c : ℂ) (hc : c ≠ 0) :
    let C := c • cliffordAlgebraMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t)))
    let D := c⁻¹ • cliffordAlgebraMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t)))
    ExactMatchgateMatrix C ∧ ExactMatchgateMatrix D ∧ C*D=1 ∧ D*C=1 := by
  have h := cliffordRowMatrix_pinElement_inverse x
  have hCD : cliffordAlgebraMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) *
      cliffordAlgebraMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) = 1 := by
    simpa only [cliffordRowMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_one] using congrArg Matrix.transpose h.2.2.2
  have hDC : cliffordAlgebraMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) *
      cliffordAlgebraMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) = 1 := by
    simpa only [cliffordRowMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_one] using congrArg Matrix.transpose h.2.2.1
  refine ⟨((cliffordAlgebraMatrix_isMatchgate_pinElement x).smul c).exactMatrix,
    ((cliffordAlgebraMatrix_isMatchgate_pinElement x⁻¹).smul c⁻¹).exactMatrix, ?_, ?_⟩ <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hCD, hDC,
      mul_inv_cancel₀ hc, inv_mul_cancel₀ hc, one_smul]

/-- Lemma10.3 for actual exact matchgate rowspaces. -/
theorem exact_rank_two_gaussian_hull {r s t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ}
    {Q : Matrix (BooleanInput s) (BooleanInput t) ℂ}
    (hP : ExactMatchgateMatrix P) (hQ : ExactMatchgateMatrix Q)
    (hrP : P.rank=2) (hrQ : Q.rank=2)
    (hne : orderedRowSpace P ≠ orderedRowSpace Q)
    (hmeet : orderedRowSpace P ⊓ orderedRowSpace Q ≠ ⊥) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank=4 ∧
      orderedRowSpace P ⊔ orderedRowSpace Q ≤ orderedRowSpace H := by
  obtain ⟨H,hH,hr,hcover⟩ := exists_rank_two_gaussian_hull hP.identities hQ.identities hrP hrQ hne hmeet
  exact ⟨H,hH.exactMatrix,hr,hcover⟩

/-- Lemma10.4 with all zero-width cases included. -/
theorem ExactMatchgateMatrix.exists_decoder {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (hP : ExactMatchgateMatrix P)
    (hr : P.rank=2^r) :
    ∃ D : Matrix (BooleanInput t) (BooleanInput r) ℂ,
      ExactMatchgateMatrix D ∧ P*D=1 := by
  obtain ⟨D,hD,hPD⟩ := hP.identities.exists_rightInverse hr
  exact ⟨D,hD.exactMatrix,hPD⟩

/-- Lemma10.5, simultaneously for every original left and right label and
arity. The same smaller base N is fixed before any tensor is selected. -/
theorem exact_labelwise_cover_compression {A : Type*} [Fintype A] {r t : ℕ}
    (M : Matrix A (BooleanInput t) ℂ) (P : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (hP : ExactMatchgateMatrix P) (hr : P.rank=2^r)
    (hcover : Submodule.span ℂ (Set.range M.row) ≤ orderedRowSpace P) :
    ∃ N : Matrix A (BooleanInput r) ℂ,
      M=N*P ∧
      (∀ k (F : (Fin k → A) → ℂ), ExactMatchgate (leftBooleanLift M k F) →
        ExactMatchgate (leftBooleanLift N k F)) ∧
      (∀ k (H : BooleanTable (k*t) ℂ), ExactMatchgate H →
        ExactMatchgate (blockwiseTransform P k H) ∧
        rightBooleanRestriction M k H = rightBooleanRestriction N k (blockwiseTransform P k H)) := by
  obtain ⟨N,D,hMP,hPD,hD,hleft,hright⟩ := exists_common_cover_compression M P hP.identities hr hcover
  refine ⟨N,hMP,?_,?_⟩
  · intro k F hF
    exact (hleft k F hF.matchgateIdentities).exactMatchgate
  · intro k H hH
    obtain ⟨hh,he⟩ := hright k H hH.matchgateIdentities
    exact ⟨hh.exactMatchgate,he⟩

end
end MatchgateWidth
