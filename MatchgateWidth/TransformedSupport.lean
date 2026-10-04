import MatchgateWidth.TensorNetwork
import MatchgateWidth.StarContraction
import MatchgateWidth.BaseDecoder
import Mathlib.Basic.Complex.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Supports of transformed tensors

The common-base transform is defined by its complete coordinate sum.  Its
flattening and complementary tensor powers are derived from that sum.
-/

namespace MatchgateWidth
noncomputable section
open scoped Classical

variable {K P D B C : Type*} [Field K]
variable [DecidableEq P] [Fintype P] [Fintype D] [Fintype B] [Fintype C]

/-- Tensor power of a base, with its actual product coefficients. -/
def tensorPowerMatrix (M : Matrix D B K) : Matrix (P → D) (P → B) K :=
  fun x y => ∏ i, M (x i) (y i)

/-- The left/common-base lift, `F M^{⊗P}`, from primitive to block labels. -/
def leftTransform (M : Matrix D B K) (F : (P → D) → K) (y : P → B) : K :=
  ∑ x : P → D, F x * ∏ i, M (x i) (y i)

omit [Fintype D] [Fintype C] in
/-- Tensor powers preserve multiplication; the intermediate assignments are summed. -/
theorem tensorPowerMatrix_mul (M : Matrix D B K) (N : Matrix B C K) :
    tensorPowerMatrix (P := P) (M * N) = tensorPowerMatrix M * tensorPowerMatrix N := by
  classical
  ext x z
  simp only [tensorPowerMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.prod_mul_distrib

omit [Fintype D] [DecidableEq P] in
/-- The tensor power of the identity has precisely the coordinate delta entries. -/
theorem tensorPowerMatrix_one :
    tensorPowerMatrix (P := P) (1 : Matrix D D K) = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorPowerMatrix]
  · have hi : ∃ i, x i ≠ y i := by
      by_contra hn
      apply h
      funext i
      exact not_ne_iff.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hi
    have hp : (∏ j, (1 : Matrix D D K) (x j) (y j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simpa [tensorPowerMatrix, h] using hp

omit [Fintype D] in
/-- Any actual base decoder lifts to a decoder on arbitrary finite port sets. -/
theorem tensorPowerMatrix_mul_decoder (M : Matrix D B K) (N : Matrix B D K)
    (h : M * N = 1) :
    tensorPowerMatrix (P := P) M * tensorPowerMatrix (P := P) N = 1 := by
  rw [← tensorPowerMatrix_mul (P := P) M N, h, tensorPowerMatrix_one (P := P)]

/-- An explicit tensor-power decoder proves complementary-coordinate surjectivity. -/
theorem tensorPowerMatrix_surjective_of_decoder (M : Matrix D B K)
    (N : Matrix B D K) (h : M * N = 1) :
    Function.Surjective (tensorPowerMatrix (P := P) M).mulVecLin := by
  classical
  intro x
  refine ⟨(tensorPowerMatrix N).mulVecLin x, ?_⟩
  have hm := tensorPowerMatrix_mul_decoder (P := P) M N h
  have he := congrArg (fun A : Matrix (P → D) (P → D) K => A.mulVecLin x) hm
  simpa [Matrix.mulVecLin_mul] using he

/-- Splitting the selected port in a finite product. -/
theorem prod_eq_selected_mul_complement (j : P) (f : P → K) :
    (∏ i, f i) = f j * ∏ i : {i : P // i ≠ j}, f i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
  congr 1
  exact Finset.prod_subtype (Finset.univ.erase j) (by simp) f

/-- Splitting the selected coordinate in the complete tensor sum. -/
theorem sum_eq_selected_sum_complement (j : P) (f : (P → D) → K) :
    (∑ x : P → D, f x) =
      ∑ d : D, ∑ a : {i : P // i ≠ j} → D, f (insertBoundaryCoordinate j d a) := by
  classical
  calc
    _ = ∑ da : D × ({i : P // i ≠ j} → D), f ((Equiv.funSplitAt j D).symm da) :=
      ((Equiv.funSplitAt j D).symm.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      funext i
      by_cases hi : i = j <;> simp [Equiv.funSplitAt_symm_apply, insertBoundaryCoordinate, hi]

omit [Fintype B] in
/-- The flattening of the actual coordinate lift factors over its complementary ports. -/
theorem portFlatten_leftTransform (M : Matrix D B K) (F : (P → D) → K) (j : P) :
    portFlatten (leftTransform M F) j =
      M.transpose * portFlatten F j * tensorPowerMatrix M := by
  classical
  ext b a
  change (∑ x : P → D, F x * ∏ i, M (x i) (insertBoundaryCoordinate j b a i)) = _
  rw [sum_eq_selected_sum_complement j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, portFlatten, tensorPowerMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [prod_eq_selected_mul_complement j]
  simp only [insertBoundaryCoordinate_same]
  have hc : (∏ i : {i : P // i ≠ j},
      M (insertBoundaryCoordinate j d c i) (insertBoundaryCoordinate j b a i)) =
      ∏ i : {i : P // i ≠ j}, M (c i) (a i) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [insertBoundaryCoordinate_ne j d c i i.property,
      insertBoundaryCoordinate_ne j b a i i.property]
  rw [hc]
  ring


omit [Fintype B] in
/-- The usual `u ↦ uM` coordinate map is multiplication by the transpose. -/
theorem transpose_mulVecLin_eq_unaryTransform (M : Matrix D B K) (u : D → K) :
    M.transpose.mulVecLin u = unaryTransform M u := by
  ext b
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, unaryTransform]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

/-- Complementary tensor powers are surjective as a consequence of base rank,
not as a separate assumption on the flattening. -/
theorem tensorPowerMatrix_surjective (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) :
    Function.Surjective (tensorPowerMatrix (P := P) M).mulVecLin := by
  classical
  obtain ⟨N, hN⟩ := exists_baseDecoder M hM
  exact tensorPowerMatrix_surjective_of_decoder M N hN

/-- The actual forward tensor-power map is injective, with the transpose of the
explicit tensor-power decoder as a left inverse. This also covers zero ports. -/
theorem tensorPowerMatrix_transpose_injective (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) :
    Function.Injective (tensorPowerMatrix (P := P) M).transpose.mulVecLin := by
  classical
  obtain ⟨N, hN⟩ := exists_baseDecoder M hM
  have hm := tensorPowerMatrix_mul_decoder (P := P) M N hN
  have ht : (tensorPowerMatrix (P := P) N).transpose *
      (tensorPowerMatrix (P := P) M).transpose = 1 := by
    rw [← Matrix.transpose_mul, hm, Matrix.transpose_one]
  have hinv : Function.LeftInverse (tensorPowerMatrix (P := P) N).transpose.mulVecLin
      (tensorPowerMatrix (P := P) M).transpose.mulVecLin := by
    intro x
    have he := congrArg (fun A : Matrix (P → D) (P → D) K => A.mulVecLin x) ht
    simpa [Matrix.mulVecLin_mul] using he
  exact hinv.injective

omit [Fintype B] in
/-- The coordinate transform is precisely the forward linear tensor-power map. -/
theorem leftTransform_eq_tensorPowerMatrix_transpose_mulVecLin
    (M : Matrix D B K) (F : (P → D) → K) :
    leftTransform M F = (tensorPowerMatrix (P := P) M).transpose.mulVecLin F := by
  rw [transpose_mulVecLin_eq_unaryTransform]
  rfl

/-- A full-row-rank base loses no information in the full tensor lift. -/
theorem leftTransform_injective (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) :
    Function.Injective (leftTransform (P := P) M) := by
  intro F G h
  apply tensorPowerMatrix_transpose_injective M hM
  simpa only [leftTransform_eq_tensorPowerMatrix_transpose_mulVecLin] using h

/-- **Transformed block supports (Lemma 10.2).** For any finite port set and
injective common base, each transformed port support is exactly the image of
the primitive support under `u ↦ uM`. The complement map is proved surjective
from a base decoder, including the empty complement of a unary tensor. -/
theorem transformed_port_support (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) (F : (P → D) → K) (j : P) :
    columnSupport (portFlatten (leftTransform M F) j) =
      (columnSupport (portFlatten F j)).map M.transpose.mulVecLin := by
  classical
  rw [portFlatten_leftTransform]
  apply columnSupport_transformed
  exact tensorPowerMatrix_surjective (P := {i : P // i ≠ j}) M hM

/-- A full-row-rank base preserves the dimension of every primitive port support. -/
theorem transformed_port_support_finrank (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) (F : (P → D) → K) (j : P) :
    Module.finrank K (columnSupport (portFlatten (leftTransform M F) j)) =
      Module.finrank K (columnSupport (portFlatten F j)) := by
  rw [transformed_port_support M hM F j]
  exact finrank_map_transpose_eq M hM _

/-- The exact support identity stated directly using full row rank. -/
theorem transformed_port_support_of_full_row_rank (M : Matrix D B K)
    (hM : M.rank = Fintype.card D) (F : (P → D) → K) (j : P) :
    columnSupport (portFlatten (leftTransform M F) j) =
      (columnSupport (portFlatten F j)).map M.transpose.mulVecLin := by
  exact transformed_port_support M (transpose_injective_of_rank_eq_card M hM) F j

/-- The dimension conclusion stated directly using full row rank. -/
theorem transformed_port_support_finrank_of_full_row_rank (M : Matrix D B K)
    (hM : M.rank = Fintype.card D) (F : (P → D) → K) (j : P) :
    Module.finrank K (columnSupport (portFlatten (leftTransform M F) j)) =
      Module.finrank K (columnSupport (portFlatten F j)) := by
  exact transformed_port_support_finrank M (transpose_injective_of_rank_eq_card M hM) F j

/-- The source's complex qutrit-to-Boolean-block setting, for every arity at
least one and every block width. Ordinary transpose, not conjugate transpose,
is used throughout. -/
theorem qutrit_booleanBlock_support (n t : ℕ)
    (M : Matrix (Fin 3) (Fin t → Bool) ℂ)
    (hM : Function.Injective M.transpose.mulVecLin)
    (F : (Fin (n + 1) → Fin 3) → ℂ) (j : Fin (n + 1)) :
    columnSupport (portFlatten (leftTransform M F) j) =
        (columnSupport (portFlatten F j)).map M.transpose.mulVecLin ∧
      Module.finrank ℂ (columnSupport (portFlatten (leftTransform M F) j)) =
        Module.finrank ℂ (columnSupport (portFlatten F j)) := by
  exact ⟨transformed_port_support M hM F j, transformed_port_support_finrank M hM F j⟩


/-- Lemma 10.2 in its rank-three complex/Boolean-block form. -/
theorem qutrit_booleanBlock_support_of_rank_three (n t : ℕ)
    (M : Matrix (Fin 3) (Fin t → Bool) ℂ) (hM : M.rank = 3)
    (F : (Fin (n + 1) → Fin 3) → ℂ) (j : Fin (n + 1)) :
    columnSupport (portFlatten (leftTransform M F) j) =
        (columnSupport (portFlatten F j)).map M.transpose.mulVecLin ∧
      Module.finrank ℂ (columnSupport (portFlatten (leftTransform M F) j)) =
        Module.finrank ℂ (columnSupport (portFlatten F j)) := by
  apply qutrit_booleanBlock_support
  apply transpose_injective_of_rank_eq_card
  simpa using hM

end
end MatchgateWidth
