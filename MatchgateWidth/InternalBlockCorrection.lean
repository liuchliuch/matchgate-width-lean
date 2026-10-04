import MatchgateWidth.AllLeftWirePorts
import MatchgateWidth.ReversedAllLeftNetwork

/-!
# Internal-only block correction with inherited exposed boundary order

Only left blocks attached to an internal edge are reversed in the local graph.
The physical ribbon reverses those blocks a second time. Exposed left blocks
are untouched both locally and at the outer boundary.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} (I : AllLeftGadget S a b c n)

/-- The actual internal ports at this occurrence of a primitive left label. -/
def internalLeftPorts (v : Fin a) : Finset (Fin (S.leftArity (I.leftLabel v))) :=
  Finset.univ.filter (fun i => ∃ e, I.leftIncidence ⟨v,i⟩ = Sum.inl e)

/-- Corrected local tensors depend on which ports are internal, not just on
the label. Original labels and tensor values are never changed in the domain. -/
def correctedLeftTensor
    (F : (l : S.LeftLabel) → BooleanTable (S.leftArity l*t) ℂ) (v : Fin a) :
    BooleanTable (S.leftArity (I.leftLabel v)*t) ℂ :=
  reverseTensorBlocks (I.internalLeftPorts v) (F (I.leftLabel v))

/-- Actual left physical assignments: internal word order reversed, exposed
boundary word order unchanged. -/
def physicalLeftWords (x : Fin c → BooleanInput t) (z : Fin n → BooleanInput t)
    (v : Fin a) : Fin (S.leftArity (I.leftLabel v)) → BooleanInput t :=
  fun i => Sum.elim (fun e => reverseBlockWord (x e)) z (I.leftIncidence ⟨v,i⟩)

/-- At every internal port the two reversals cancel, while an exposed port is
unchanged. This is the exact coefficient identity needed by physical gluing. -/
theorem correctedLeftTensor_physical
    (F : (l : S.LeftLabel) → BooleanTable (S.leftArity l*t) ℂ)
    (x : Fin c → BooleanInput t) (z : Fin n → BooleanInput t) (v : Fin a) :
    I.correctedLeftTensor F v (flattenBooleanBlocks (I.physicalLeftWords x z v)) =
      F (I.leftLabel v) (flattenBooleanBlocks
        (fun i => Sum.elim x z (I.leftIncidence ⟨v,i⟩))) := by
  unfold correctedLeftTensor
  rw [reverseTensorBlocks_blocks]
  apply congrArg (F (I.leftLabel v))
  apply congrArg flattenBooleanBlocks
  funext i
  cases he : I.leftIncidence ⟨v,i⟩ with
  | inl e => simp [reverseBlockAssignment, internalLeftPorts, physicalLeftWords, he]
  | inr p => simp [reverseBlockAssignment, internalLeftPorts, physicalLeftWords, he]

/-- Opposite-position internal ribbons and the inherited boundary order. -/
def internalPhysicalNetwork
    (L : (v : Fin a) → BooleanTable (S.leftArity (I.leftLabel v)*t) ℂ)
    (R : (l : S.RightLabel) → BooleanTable (S.rightArity l*t) ℂ)
    (z : Fin n → BooleanInput t) : ℂ :=
  ∑ x : Fin c → BooleanInput t,
    (∏ v, L v (flattenBooleanBlocks (I.physicalLeftWords x z v))) *
      ∏ v, R (I.rightLabel v) (flattenBooleanBlocks (fun i => x (I.rightIncidence ⟨v,i⟩)))

/-- Exact local correction and genuine opposite-position internal wiring give
the original boundary lift without reversing any exposed block. -/
theorem internalPhysicalNetwork_presentation_eq_lift
    (p : LabelledCommonPresentation S (Fin 3) t) :
    I.internalPhysicalNetwork
      (I.correctedLeftTensor (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l)))
      p.rightPreimage = leftTransform p.baseMatrix (I.value p.language) := by
  rw [← reversedPhysicalNetwork_presentation_eq_lift I p]
  funext z
  unfold internalPhysicalNetwork reversedPhysicalNetwork reversedLeftLocal
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [I.correctedLeftTensor_physical, reverseBlockWord_involutive]

/-- Every internally corrected local tensor has a genuine exact graph
realization. The finite internal-port selection is handled uniformly. -/
theorem correctedLeftTensor_exact
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3) (v : Fin a) :
    ExactMatchgate (I.correctedLeftTensor
      (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l)) v) := by
  have hF : ExactMatchgate (leftBooleanLift p.baseMatrix (S.leftArity (I.leftLabel v))
      (p.left (I.leftLabel v))) :=
    (exactMatchgate_iff_booleanDiskRealizable _).mpr (p.validLeft (I.leftLabel v))
  exact (hF.matchgateIdentities.reverse_tensor_blocks
    (exact_qutrit_lift_block_rank_le_two p.baseMatrix hM _ hF) (I.internalLeftPorts v)).exactMatchgate

end AllLeftGadget
end
end MatchgateWidth
