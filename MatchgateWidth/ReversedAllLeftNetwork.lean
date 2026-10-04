import MatchgateWidth.AllBlockReversal
import MatchgateWidth.AllLeftGadgetHolography

/-!
# Exact reversed-ribbon wiring identity

Each left local signature is corrected by reversing each complete Boolean block.
Every physical bridge then identifies opposite positions in the two locally
ordered boundary blocks. External left boundary words use that same reversed
local position. The two reversals cancel exactly, giving the original lift.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

private theorem leftTransform_decidableEq_eq {n t : ℕ}
    (d₁ d₂ : DecidableEq (Fin n)) (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (T : (Fin n → Fin 3) → ℂ) :
    (letI := d₁; leftTransform M T) = (letI := d₂; leftTransform M T) := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

/-- All left local blocks are reversed, without changing label or arity. -/
def reversedLeftLocal {S : LabelledShape} {t : ℕ}
    (L : (l : S.LeftLabel) → BooleanTable (S.leftArity l*t) ℂ)
    (l : S.LeftLabel) : (Fin (S.leftArity l) → BooleanInput t) → ℂ :=
  fun x => L l (flattenBooleanBlocks (fun i => reverseBlockWord (x i)))

/-- The actual finite network sum for opposite-position physical ribbons.
Right positions are the global word positions; all left positions, including
external ones, are reversed within their own blocks. -/
def reversedPhysicalNetwork {S : LabelledShape} {a b c n t : ℕ}
    (I : AllLeftGadget S a b c n)
    (L : (l : S.LeftLabel) → (Fin (S.leftArity l) → BooleanInput t) → ℂ)
    (R : (l : S.RightLabel) → BooleanTable (S.rightArity l*t) ℂ)
    (z : Fin n → BooleanInput t) : ℂ :=
  ∑ x : Fin c → BooleanInput t,
    (∏ v, L (I.leftLabel v)
      (fun i => reverseBlockWord (Sum.elim x z (I.leftIncidence ⟨v,i⟩)))) *
    ∏ v, R (I.rightLabel v) (flattenBooleanBlocks (fun i => x (I.rightIncidence ⟨v,i⟩)))

/-- Opposite-position ribbon wiring exactly cancels the local correction.
This is equality of actual finite sums, not a diagrammatic convention. -/
theorem reversedPhysicalNetwork_corrected_eq {S : LabelledShape} {a b c n t : ℕ}
    (I : AllLeftGadget S a b c n)
    (L : (l : S.LeftLabel) → BooleanTable (S.leftArity l*t) ℂ)
    (R : (l : S.RightLabel) → BooleanTable (S.rightArity l*t) ℂ)
    (z : Fin n → BooleanInput t) :
    reversedPhysicalNetwork I (reversedLeftLocal L) R z =
      I.value { left := fun l x => L l (flattenBooleanBlocks x)
                right := fun l x => R l (flattenBooleanBlocks x) } z := by
  rw [AllLeftGadget.value_eq]
  simp only [reversedPhysicalNetwork, reversedLeftLocal, reverseBlockWord_involutive]
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  rfl

/-- Each corrected left local tensor is still an actual exact matchgate.
The proof derives all block ranks at most two before reversing them. -/
theorem LabelledCommonPresentation.reversedLeftLocal_exact {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (l : S.LeftLabel) :
    ExactMatchgate (reverseTensorBlocks Finset.univ
      (leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l))) := by
  apply exact_qutrit_lift_reverse_all_blocks p.baseMatrix hM
  exact (exactMatchgate_iff_booleanDiskRealizable _).mpr (p.validLeft l)

/-- The physical corrected Boolean network has exactly the boundary lift of
the original qutrit-domain gadget. No unproved matchgate closure is invoked. -/
theorem reversedPhysicalNetwork_presentation_eq_lift {S : LabelledShape} {a b c n t : ℕ}
    (I : AllLeftGadget S a b c n) (p : LabelledCommonPresentation S (Fin 3) t) :
    reversedPhysicalNetwork I
      (reversedLeftLocal (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l)))
      p.rightPreimage = leftTransform p.baseMatrix (I.value p.language) := by
  funext z
  rw [reversedPhysicalNetwork_corrected_eq]
  have h := I.leftTransform_value p.baseMatrix p.left
    (fun l x => p.rightPreimage l (flattenBooleanBlocks x))
  have he : (AllLeftGadget.liftedLanguage p.baseMatrix p.left
      (fun l x => p.rightPreimage l (flattenBooleanBlocks x))) =
      { left := fun l x => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l)
          (flattenBooleanBlocks x)
        right := fun l x => p.rightPreimage l (flattenBooleanBlocks x) } := by
    unfold AllLeftGadget.liftedLanguage
    apply congrArg (fun X => LabelledLanguage.mk X
      (fun l x => p.rightPreimage l (flattenBooleanBlocks x)))
    funext l x
    symm
    calc
      _ = leftTransform p.baseMatrix (p.left l) x :=
        congrArg (leftTransform p.baseMatrix (p.left l)) (blockCoordinates_flatten x)
      _ = _ := congrFun (leftTransform_decidableEq_eq _ _ p.baseMatrix (p.left l)) x
  rw [he] at h
  calc
    _ = _ := congrFun h.symm z
    _ = leftTransform p.baseMatrix (I.value p.language) z :=
      congrFun (leftTransform_decidableEq_eq _ _ p.baseMatrix (I.value p.language)) z

end
end MatchgateWidth
