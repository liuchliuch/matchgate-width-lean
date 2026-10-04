import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Decoders for full-row-rank bases

An injective transpose gives a right inverse for the base matrix.  The proof
uses equality of row and column rank over an arbitrary field, rather than an
inner product or a positive-definiteness assumption.
-/

namespace MatchgateWidth

noncomputable section

variable {K D B : Type*} [Field K] [Fintype D] [Fintype B]

/-- Injectivity of the transpose is the full-row-rank condition. -/
theorem rank_eq_card_of_transpose_injective (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) :
    M.rank = Fintype.card D := by
  rw [← Matrix.rank_transpose M, Matrix.rank,
    LinearMap.finrank_range_of_inj hM, Module.finrank_pi]

/-- Full row rank makes the transposed base injective. -/
theorem transpose_injective_of_rank_eq_card (M : Matrix D B K)
    (hM : M.rank = Fintype.card D) :
    Function.Injective M.transpose.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  change M.transpose.rank + _ = _ at h
  rw [Matrix.rank_transpose, hM, Module.finrank_pi] at h
  exact Nat.add_left_cancel (h.trans (Nat.add_zero _).symm)

/-- Equivalence between full row rank and injectivity of the transposed base. -/
theorem transpose_injective_iff_rank_eq_card (M : Matrix D B K) :
    Function.Injective M.transpose.mulVecLin ↔ M.rank = Fintype.card D := by
  exact ⟨rank_eq_card_of_transpose_injective M, transpose_injective_of_rank_eq_card M⟩

/-- A full-row-rank base maps onto its row-coordinate space. -/
theorem mulVecLin_surjective_of_transpose_injective (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) :
    Function.Surjective M.mulVecLin := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change M.rank = Module.finrank K (D → K)
  rw [rank_eq_card_of_transpose_injective M hM, Module.finrank_pi]

/-- Every full-row-rank base has a decoder. -/
theorem exists_baseDecoder (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) [DecidableEq D] :
    ∃ N : Matrix B D K, M * N = 1 := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mp
  exact mulVecLin_surjective_of_transpose_injective M hM

omit [Fintype B] in
/-- Mapping a support through an injective transposed base preserves its dimension. -/
theorem finrank_map_transpose_eq (M : Matrix D B K)
    (hM : Function.Injective M.transpose.mulVecLin) (S : Submodule K (D → K)) :
    Module.finrank K (S.map M.transpose.mulVecLin) = Module.finrank K S := by
  exact (Submodule.equivMapOfInjective M.transpose.mulVecLin hM S).finrank_eq.symm

end

end MatchgateWidth
