import MatchgateWidth.AllLeftSupportGeometry
import MatchgateWidth.BlockSupportExtraction

/-! # Actual support extraction follows from exact ordered gadget lifting

Only the geometric substitution/lifting obligation remains. Cyclic rerooting,
transpose, actual rowspace equality, purity, and ranks are all derived here.
-/
namespace MatchgateWidth
noncomputable section

/-- Unconditional algebraic extraction from a full-rank base and an exact
lift. The selected block retains its internal order; only complementary
columns receive the prescribed ordered-matrix reversal. -/
theorem exact_lift_block_rowSpace {n t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    (T : (Fin n → Fin 3) → ℂ) (hT : ExactMatchgate (leftBooleanLift M n T)) (j : Fin n) :
    ∃ A : Matrix (BooleanInput ((n-1)*t)) (BooleanInput t) ℂ,
      ExactMatchgateMatrix A ∧ orderedRowSpace A =
        (columnSupport (portFlatten T j)).map M.transpose.mulVecLin := by
  obtain ⟨A, hA, hrow⟩ := hT.exists_block_rowSpace j
  have he : (fun x => leftBooleanLift M n T (flattenBooleanBlocks x)) = leftTransform M T := by
    funext x
    unfold leftBooleanLift
    change leftTransform M T ((booleanBlocksEquiv n t).symm ((booleanBlocksEquiv n t) x)) = _
    rw [Equiv.symm_apply_apply]
  rw [he, transformed_port_support_of_full_row_rank M (by simpa using hM)] at hrow
  exact ⟨A, hA, hrow⟩

/-- The earlier named extraction interface is now a theorem from exact lifting,
not an additional hypothesis on source gadget supports. -/
theorem allLeftPlaneExtraction_of_exactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) : AllLeftPlaneExtraction p := by
  intro a b c n I hconn hplan hne j hr
  obtain ⟨A, hA, hrow⟩ := exact_lift_block_rowSpace p.baseMatrix hM (I.value p.language)
    (hlift a b c n I hconn hplan) j
  exact ⟨(n-1)*t, A, hA, hrow⟩

/-- Actual realized Gaussian support geometry requires only exact lifting;
there is no separate rank-two rowspace or pure-ray assumption. -/
def allLeftExactSupportGeometry {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) : RealizedMatchgateGeometry t :=
  allLeftMatchgateGeometry p hM hlift (allLeftPlaneExtraction_of_exactLifting p hM hlift)

end
end MatchgateWidth
