import MatchgateWidth.ControlledLabelledPresentation

/-! # Literal rational coefficients for the displayed labelled presentation

The right preimage is formed over the rationals and then embedded into the
complex numbers. Its identities supply actual rational-edge disk witnesses.
This avoids requiring an implicit coefficient-field identification of the
independently constructed complex Pfaffian signature.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000

/-- Every displayed coefficient, including the actual Boolean preimages, is
rational. The valid matchgate graphs are already part of the presentation. -/
def RationalCoefficientPresentation {S : LabelledShape} {E : Type} [Fintype E]
    {r : ℕ} (p : LabelledCommonPresentation S E r) : Prop :=
  (∀ d z, ∃ q : ℚ, p.base d z = q) ∧
  (∀ l x, ∃ q : ℚ, p.left l x = q) ∧
  (∀ l z, ∃ q : ℚ, p.rightPreimage l z = q)

/-- The rational preimage, cast along equality of the certified boundary length. -/
def rationalControlledLabelledPreimage {k : ℕ} (f : BooleanTable k ℚ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) : BooleanTable ((k + 2) * (2 ^ k + 3)) ℚ :=
  castBooleanTable (controlledPhysicalOrder_length k) (controlledBooleanPreimage f hf j)

/-- Actual common presentation using the rational preimage literally. -/
def rationalControlledLabelledPresentation {k : ℕ} (f : BooleanTable k ℚ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    LabelledCommonPresentation (starLanguageShape (k + 2)) (Fin 3) (2 ^ k + 3) where
  base := controlledLabelledBase k
  left := (controlledLabelledLanguage (fun x => (f x : ℂ)) j).left
  rightPreimage _ z := (rationalControlledLabelledPreimage f hf j z : ℂ)
  validLeft := (controlledLabelledPresentation (fun x => (f x : ℂ))
    (fun x => Rat.cast_ne_zero.mpr (hf x)) j).validLeft
  validRight _ := by
    obtain ⟨v,e,G,ext,hd,hw,hs⟩ := ((controlledBooleanPreimage_mgi f hf j).cast
      (controlledPhysicalOrder_length k)).rational_diskWitness_all
    exact ⟨v,e,G,ext,hd,fun y => (hs y).symm⟩

/-- Restriction of the rational preimage to the displayed codewords. -/
theorem rationalControlledLabelledPreimage_code {k : ℕ} (f : BooleanTable k ℚ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) (x : Fin (k + 2) → Fin 3) :
    rationalControlledLabelledPreimage f hf j
      (flattenBooleanBlocks (fun p =>
        (booleanWordEquiv (2 ^ k + 3)).symm (controlledCode k (x p)))) =
      controlledQutrit f j (Sum.elim (fun l : Fin 2 => if l = 0 then x 0 else x 1)
        (fun i => x i.succ.succ)) := by
  let r : ControlledQutritPort k → Fin 3 :=
    Sum.elim (fun l => if l = 0 then x 0 else x 1) (fun i => x i.succ.succ)
  have hr : ∀ p, r (controlledLabelledPort k p) = x p := by
    intro p
    induction p using Fin.cases with
    | zero => simp [r,controlledLabelledPort]
    | succ p =>
      induction p using Fin.cases with
      | zero => simp [r,controlledLabelledPort]
      | succ p => simp [r,controlledLabelledPort]
  unfold rationalControlledLabelledPreimage castBooleanTable
  have hz : (flattenBooleanBlocks (fun p =>
      (booleanWordEquiv (2 ^ k + 3)).symm (controlledCode k (x p))) ∘
      Fin.cast (controlledPhysicalOrder_length k)) =
      (orderedBooleanAssignment (controlledPhysicalOrder k)
        (controlledPhysicalOrder_nodup k) mem_controlledPhysicalOrder).symm
        (fun m => controlledCode k (r m.1) m.2) := by
    funext t
    simp only [Function.comp_apply, orderedBooleanAssignment_symm_apply,
      controlledPhysicalOrder_get, controlledLabelledMode, hr]
    rfl
  rw [hz, controlledBooleanPreimage_code]

/-- The rational construction recovers exactly the complex source language. -/
theorem rationalControlledLabelledPresentation_language {k : ℕ} (f : BooleanTable k ℚ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    (rationalControlledLabelledPresentation f hf j).language =
      controlledLabelledLanguage (fun x => (f x : ℂ)) j := by
  have hr : (rationalControlledLabelledPresentation f hf j).language.right =
      (controlledLabelledLanguage (fun x => (f x : ℂ)) j).right := by
    funext l x
    change rightTransform (controlledLabelledBase k)
      (fun y => ((rationalControlledLabelledPreimage f hf j (flattenBooleanBlocks y)) : ℂ)) x = _
    rw [controlledLabelledBase, rightTransform_coordinateBase,
      rationalControlledLabelledPreimage_code]
    simp only [controlledLabelledLanguage, orderedControlledQutrit,
      controlledQutrit, hardControlWeight]
    split_ifs <;> push_cast <;> rfl
  have hl : (rationalControlledLabelledPresentation f hf j).language.left =
      (controlledLabelledLanguage (fun x => (f x : ℂ)) j).left := rfl
  cases h : controlledLabelledLanguage (fun x => (f x : ℂ)) j
  cases h' : (rationalControlledLabelledPresentation f hf j).language
  simp only [h,h'] at hl hr
  congr

/-- Rationality applies to every entry of all five displayed components. -/
theorem rationalControlledLabelledPresentation_rational {k : ℕ} (f : BooleanTable k ℚ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    RationalCoefficientPresentation (rationalControlledLabelledPresentation f hf j) := by
  refine ⟨?_,?_,?_⟩
  · intro d z
    change ∃ q : ℚ, controlledLabelledBase k d z = q
    unfold controlledLabelledBase coordinateBase
    split_ifs
    · exact ⟨1,by norm_num⟩
    · exact ⟨0,by norm_num⟩
  · intro l x
    cases l with
    | inl r =>
      simp only [rationalControlledLabelledPresentation, controlledLabelledLanguage, coordinatePin]
      split_ifs
      · exact ⟨1,by norm_num⟩
      · exact ⟨0,by norm_num⟩
    | inr u =>
      change ∃ q : ℚ, (if (x 0 = 0 ∧ x 1 = 1) ∨ (x 0 = 1 ∧ x 1 = 0)
        then (1 : ℂ) else 0) = q
      split_ifs
      · exact ⟨1,by norm_num⟩
      · exact ⟨0,by norm_num⟩
  · intro l z
    exact ⟨rationalControlledLabelledPreimage f hf j z,rfl⟩

end
end MatchgateWidth
