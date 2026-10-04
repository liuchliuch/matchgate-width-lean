import MatchgateWidth.MGIRowSpaceBasis
import MatchgateWidth.CoverCompressionAlgebra
import MatchgateWidth.MGICyclicRotation

/-! # Reversal of a rank-at-most-two ordered block
The restriction on rank is essential: unsigned block reversal is not a general
matchgate operation. The proof factors through at most one Boolean wire.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {r t : ℕ}

/-- Reversing both matrix index orders is reflection followed by cyclic rerooting. -/
theorem OrderedMatchgateMatrix.reverse_both_blocks
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) :
    OrderedMatchgateMatrix (fun x y => P (fun i => x i.rev) (fun j => y j.rev)) := by
  have h := BooleanMatchgateIdentities.rotateBlocks hP.transpose
  have heq : (fun z : BooleanInput (r+t) =>
      orderedMatrixSignature P.transpose (fun i => z (finAddFlip i))) =
      orderedMatrixSignature (fun x y => P (fun i => x i.rev) (fun j => y j.rev)) := by
    funext z
    unfold orderedMatrixSignature
    change P _ _ = P _ _
    congr 1
    · funext i
      simp only [finAddFlip_apply_natAdd]
    · funext j
      simp only [finAddFlip_apply_castAdd, Fin.rev_rev]
  change BooleanMatchgateIdentities _
  rw [heq] at h
  exact h

/-- At most one input wire has no nontrivial reversal. -/
theorem OrderedMatchgateMatrix.reverse_output_of_input_le_one
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : r ≤ 1) :
    OrderedMatchgateMatrix (fun x y => P x (fun j => y j.rev)) := by
  have h := hP.reverse_both_blocks
  have hi (i : Fin r) : i.rev = i := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  simpa only [hi] using h

/-- Any rank-one or rank-two row space factors through zero or one wire;
reversing its output coordinates therefore preserves all matchgate identities. -/
theorem OrderedMatchgateMatrix.reverse_output_of_rank_pow
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) {b : ℕ} (hb : b ≤ 1) (hr : P.rank = 2^b) :
    OrderedMatchgateMatrix (fun x y => P x (fun j => y j.rev)) := by
  obtain ⟨Q,hQ,hQr,hspace⟩ := hP.exists_fullRow_cover hr
  obtain ⟨E,hE,hQE⟩ := hQ.exists_rightInverse hQr
  have hfactor : (P*E)*Q=P := matrix_factor_through_decoder P Q E hQE (le_of_eq hspace.symm)
  have h := (hP.mul hE).mul (hQ.reverse_output_of_input_le_one hb)
  let Qrev : Matrix (BooleanInput b) (BooleanInput t) K := fun x y => Q x (fun j => y j.rev)
  let Prev : Matrix (BooleanInput r) (BooleanInput t) K := fun x y => P x (fun j => y j.rev)
  have heq : (P*E)*Qrev = Prev := by
    ext x y
    exact congrFun (congrFun hfactor x) (fun j => y j.rev)
  change OrderedMatchgateMatrix Prev
  change OrderedMatchgateMatrix ((P*E)*Qrev) at h
  exact heq ▸ h

/-- Rank at most two includes the zero tensor; no nonvanishing is assumed. -/
theorem OrderedMatchgateMatrix.reverse_output_of_rank_le_two
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank ≤ 2) :
    OrderedMatchgateMatrix (fun x y => P x (fun j => y j.rev)) := by
  rcases Nat.eq_zero_or_pos P.rank with hz | hp
  · have hs : orderedRowSpace P = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rw [Matrix.rank_eq_finrank_span_row] at hz
      exact hz
    have hzero : P = 0 := by
      ext x y
      have hx := row_mem_orderedRowSpace P x
      rw [hs, Submodule.mem_bot] at hx
      exact congrFun hx y
    subst P
    intro A B
    simp [orderedMatrixSignature,  matchgateSum]
  · rcases (show P.rank = 1 ∨ P.rank = 2 by omega) with h1 | h2
    · exact hP.reverse_output_of_rank_pow (b := 0) (by omega) (by simpa using h1)
    · exact hP.reverse_output_of_rank_pow (b := 1) (by omega) (by simpa using h2)

/-- The same justified operation at the input block. -/
theorem OrderedMatchgateMatrix.reverse_input_of_rank_le_two
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank ≤ 2) :
    OrderedMatchgateMatrix (fun x y => P (fun i => x i.rev) y) := by
  have h := hP.transpose.reverse_output_of_rank_le_two (by simpa using hr)
  exact h.transpose

/-- The physical flattening with exactly the ordered-matrix output reversal. -/
def boundaryMatrix (F : BooleanTable (r+t) K) : Matrix (BooleanInput r) (BooleanInput t) K :=
  fun x y => F (matrixBoundaryWord x y)

@[simp] theorem orderedMatrixSignature_boundaryMatrix (F : BooleanTable (r+t) K) :
    orderedMatrixSignature (boundaryMatrix F) = F := by
  funext z
  unfold orderedMatrixSignature boundaryMatrix matrixBoundaryWord
  apply congrArg F
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

/-- Reversal of the first consecutive physical block is valid under its true
flattening-rank bound. Complementary output permutation does not change rank. -/
theorem BooleanMatchgateIdentities.reverse_first_block_of_rank_le_two
    {F : BooleanTable (r+t) K} (hF : BooleanMatchgateIdentities F)
    (hr : (boundaryMatrix F).rank ≤ 2) :
    BooleanMatchgateIdentities (fun z => F
      (Fin.append (fun i => z (Fin.castAdd t i.rev)) (fun j => z (Fin.natAdd r j)))) := by
  have hP : OrderedMatchgateMatrix (boundaryMatrix F) := by
    change BooleanMatchgateIdentities _
    simpa only [orderedMatrixSignature_boundaryMatrix] using hF
  have h := hP.reverse_input_of_rank_le_two hr
  change BooleanMatchgateIdentities _ at h
  change BooleanMatchgateIdentities (fun z => F (Fin.append
    (fun i => z (Fin.castAdd t i.rev)) (fun j => z (Fin.natAdd r j.rev.rev)))) at h
  simpa only [Fin.rev_rev] using h

end
end MatchgateWidth
