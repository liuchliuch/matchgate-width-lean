import MatchgateWidth.MGIBlockTransform
import MatchgateWidth.FullRowMatchgateDecoder
import MatchgateWidth.MGIMatrixTranspose
import MatchgateWidth.RankTwoGaussianHull

/-! # Label-preserving common-cover compression
All formulas are actual finite sums and tensor powers. Labels are unchanged
because the statements hold separately for the same arbitrary input tensor.
-/
namespace MatchgateWidth
noncomputable section
variable {K A B C I : Type*} [Field K]

section Algebra
variable [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

theorem leftTransform_compose (M : Matrix A B K) (N : Matrix B C K)
    (F : (I → A) → K) :
    leftTransform N (leftTransform M F) = leftTransform (M*N) F := by
  classical
  funext z
  simp only [leftTransform, Matrix.mul_apply]
  simp_rw [Fintype.prod_sum, Finset.sum_mul, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  apply Finset.sum_congr (by ext y; simp)
  intro y _
  ring

theorem rightTransform_compose (M : Matrix A B K) (N : Matrix B C K)
    (F : (I → C) → K) :
    rightTransform M (rightTransform N F) = rightTransform (M*N) F := by
  classical
  funext x
  simp only [rightTransform, Matrix.mul_apply]
  simp_rw [Fintype.prod_sum, Finset.sum_mul, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext y; simp)
  intro y _
  apply Finset.sum_congr (by ext z; simp)
  intro z _
  ring

theorem rightTransform_transpose (M : Matrix A B K) (F : (I → A) → K) :
    rightTransform M.transpose F = leftTransform M F := by
  classical
  funext y
  simp only [rightTransform, leftTransform, Matrix.transpose_apply]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  rfl
end Algebra

/-- A right decoder yields exact factorization of every covered row, with no
rank hypothesis on the smaller domain base. -/
theorem matrix_factor_through_decoder [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] (M : Matrix A C K) (P : Matrix B C K) (D : Matrix C B K)
    (hPD : P*D=1)
    (hcover : Submodule.span K (Set.range M.row) ≤ Submodule.span K (Set.range P.row)) :
    (M*D)*P=M := by
  have hrow (u : C → K) (hu : u ∈ Submodule.span K (Set.range P.row)) :
      Matrix.vecMul (Matrix.vecMul u D) P = u := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i,rfl⟩ := hu
      funext j
      change ((P*D)*P) i j = P i j
      rw [hPD, Matrix.one_mul]
    | zero => simp
    | add x y hx hy ihx ihy => simp [Matrix.add_vecMul, ihx, ihy]
    | smul c x hx ih => simp [Matrix.smul_vecMul, ih]
  ext i j
  exact congrFun (hrow (M.row i) (hcover (Submodule.subset_span ⟨i,rfl⟩))) j

/-- Literal block-major left lift. -/
def leftBooleanLift {r : ℕ} [Fintype A] (M : Matrix A (BooleanInput r) K)
    (k : ℕ) (F : (Fin k → A) → K) : BooleanTable (k*r) K :=
  fun z => leftTransform M F ((booleanBlocksEquiv k r).symm z)

/-- Literal block-major induced right tensor. -/
def rightBooleanRestriction {r : ℕ} [Fintype A] (M : Matrix A (BooleanInput r) K)
    (k : ℕ) (H : BooleanTable (k*r) K) : (Fin k → A) → K :=
  rightTransform M (fun x => H (flattenBooleanBlocks x))

/-- Attaching the decoder separately at each output block gives exactly the
left lift through the smaller base. -/
theorem blockwiseTransform_leftLift {r t : ℕ} [Fintype A]
    (M : Matrix A (BooleanInput t) K) (D : Matrix (BooleanInput t) (BooleanInput r) K)
    (k : ℕ) (F : (Fin k → A) → K) :
    blockwiseTransform D.transpose k (leftBooleanLift M k F) = leftBooleanLift (M*D) k F := by
  funext z
  simp only [blockwiseTransform, leftBooleanLift]
  have heq : (fun x => leftTransform M F
      ((booleanBlocksEquiv k t).symm (flattenBooleanBlocks x))) = leftTransform M F := by
    funext x
    change leftTransform M F ((booleanBlocksEquiv k t).symm ((booleanBlocksEquiv k t) x)) = _
    rw [Equiv.symm_apply_apply]
  rw [heq, rightTransform_transpose, leftTransform_compose]

/-- Right-label values remain exactly unchanged through the factorized base. -/
theorem rightRestriction_blockwiseTransform {r t : ℕ} [Fintype A]
    (N : Matrix A (BooleanInput r) K) (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (k : ℕ) (H : BooleanTable (k*t) K) :
    rightBooleanRestriction N k (blockwiseTransform P k H) =
      rightBooleanRestriction (N*P) k H := by
  unfold rightBooleanRestriction blockwiseTransform
  have heq : (fun x => rightTransform P (fun y => H (flattenBooleanBlocks y))
      ((booleanBlocksEquiv k r).symm (flattenBooleanBlocks x))) =
      rightTransform P (fun y => H (flattenBooleanBlocks y)) := by
    funext x
    change rightTransform P (fun y => H (flattenBooleanBlocks y))
      ((booleanBlocksEquiv k r).symm ((booleanBlocksEquiv k r) x)) = _
    rw [Equiv.symm_apply_apply]
  rw [heq, rightTransform_compose]

/-- Exact all-arity, labelwise algebraic form of the common-cover compression
lemma. No competing-domain or base rank assumption is introduced. -/
theorem exists_common_cover_compression {r t : ℕ} [CharZero K] [Fintype A]
    (M : Matrix A (BooleanInput t) K) (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (hP : OrderedMatchgateMatrix P) (hrank : P.rank = 2^r)
    (hcover : Submodule.span K (Set.range M.row) ≤ orderedRowSpace P) :
    ∃ (N : Matrix A (BooleanInput r) K) (D : Matrix (BooleanInput t) (BooleanInput r) K),
      M=N*P ∧ P*D=1 ∧ OrderedMatchgateMatrix D ∧
      (∀ k (F : (Fin k → A) → K), BooleanMatchgateIdentities (leftBooleanLift M k F) →
        BooleanMatchgateIdentities (leftBooleanLift N k F)) ∧
      (∀ k (H : BooleanTable (k*t) K), BooleanMatchgateIdentities H →
        BooleanMatchgateIdentities (blockwiseTransform P k H) ∧
        rightBooleanRestriction M k H = rightBooleanRestriction N k (blockwiseTransform P k H)) := by
  obtain ⟨D,hD,hPD⟩ := hP.exists_rightInverse hrank
  have hf := matrix_factor_through_decoder M P D hPD hcover
  refine ⟨M*D,D,hf.symm,hPD,hD,?_,?_⟩
  · intro k F hF
    rw [← blockwiseTransform_leftLift]
    exact hD.transpose.blockwiseTransform k hF
  · intro k H hH
    refine ⟨hP.blockwiseTransform k hH, ?_⟩
    rw [rightRestriction_blockwiseTransform, hf]

end
end MatchgateWidth
