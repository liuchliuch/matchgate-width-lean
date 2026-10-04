import MatchgateWidth.AlgebraicQutritLanguage
import MatchgateWidth.LabelledStarInstances
import MatchgateWidth.StrongExteriorAccess

/-!
# Ordered finite-width presentations of controlled labelled languages

The two link blocks precede the hard blocks, and every physical wire retains
its original position. Only equality casts of lengths are used in the Boolean
matchgate identities.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- The original port order, beginning with the two links. -/
def controlledLabelledPort (k : ℕ) : Fin (k + 2) → ControlledQutritPort k :=
  Fin.cons (.inl 0) (Fin.cons (.inl 1) Sum.inr)

private theorem controlledPortOrder_eq_ofFn (k : ℕ) :
    controlledPortOrder k = List.ofFn (controlledLabelledPort k) := by
  simp [controlledPortOrder, controlledLabelledPort,
    List.finRange, List.map_ofFn, Function.comp_def]

private theorem controlledPhysicalBlock_eq_ofFn {k : ℕ} (p : ControlledQutritPort k) :
    controlledPhysicalBlock p = List.ofFn (fun i : Fin (2 ^ k + 3) => (p, i)) := by
  unfold controlledPhysicalBlock
  simp only [List.finRange, List.map_ofFn]
  rw [List.ofFn_congr (controlledModeBlock_length p)]
  simp

/-- Reading a flattened index retains both its block and its wire position. -/
def controlledLabelledMode (k : ℕ) (t : Fin ((k + 2) * (2 ^ k + 3))) :
    ControlledPhysicalMode k :=
  (controlledLabelledPort k (finProdFinEquiv.symm t).1,
    (finProdFinEquiv.symm t).2)

/-- The certified physical list is literally the block-major enumeration. -/
theorem controlledPhysicalOrder_eq_ofFn (k : ℕ) :
    controlledPhysicalOrder k = List.ofFn (controlledLabelledMode k) := by
  unfold controlledPhysicalOrder
  rw [controlledPortOrder_eq_ofFn, List.ofFn_mul]
  simp only [List.flatMap, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext p
  dsimp only [Function.comp_def]
  rw [controlledPhysicalBlock_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  unfold controlledLabelledMode
  have he : (⟨p.val * (2 ^ k + 3) + i.val, by
      have hp := p.isLt; have hi := i.isLt; nlinarith⟩ :
      Fin ((k + 2) * (2 ^ k + 3))) = finProdFinEquiv (p, i) := by
    apply Fin.ext
    simp [Nat.mul_comm, Nat.add_comm]
  rw [he, Equiv.symm_apply_apply]

/-- Position-by-position identification, using only the proved length equality. -/
theorem controlledPhysicalOrder_get (k : ℕ)
    (t : Fin (controlledPhysicalOrder k).length) :
    (controlledPhysicalOrder k).get t =
      controlledLabelledMode k (Fin.cast (controlledPhysicalOrder_length k) t) := by
  have h := congrArg (fun xs : List (ControlledPhysicalMode k) => xs[t.val]?)
    (controlledPhysicalOrder_eq_ofFn k)
  simpa only [List.get_eq_getElem, Fin.cast, List.getElem?_eq_getElem t.isLt, List.getElem?_ofFn,
    dite_eq_left (show t.val < (k + 2) * (2 ^ k + 3) by
      simpa only [← controlledPhysicalOrder_length] using t.isLt), Option.some.injEq] using h

/-- The common coordinate base, with Boolean values encoded by `Fin 2`. -/
def controlledLabelledBase (k : ℕ) : Fin 3 → BooleanInput (2 ^ k + 3) → ℂ :=
  coordinateBase (fun r => (booleanWordEquiv (2 ^ k + 3)).symm (controlledCode k r))

private theorem controlledLabelledBase_apply (k : ℕ) (r : Fin 3)
    (z : BooleanInput (2 ^ k + 3)) :
    controlledLabelledBase k r z =
      controlledCoordinateBase k r (booleanWordEquiv (2 ^ k + 3) z) := by
  simp [controlledLabelledBase, controlledCoordinateBase, coordinateBase,
    Equiv.eq_symm_apply]

private theorem controlledLabelledLeft_eq {k n : ℕ} (F : (Fin n → Fin 3) → ℂ) :
    (fun z => leftTransform (controlledLabelledBase k) F
      (fun i t => z (finProdFinEquiv (i,t)))) = controlledLeftBoolean n F := by
  funext z
  simp only [leftTransform, controlledLeftBoolean, controlledLabelledBase_apply]
  rfl

/-- The original preimage, transported along equality of its boundary length. -/
def controlledLabelledPreimage {k : ℕ} (f : BooleanTable k ℂ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) : BooleanTable ((k + 2) * (2 ^ k + 3)) ℂ :=
  castBooleanTable (controlledPhysicalOrder_length k) (controlledBooleanPreimage f hf j)

/-- A common exact disk-matchgate presentation of all five source labels. -/
def controlledLabelledPresentation {k : ℕ} (f : BooleanTable k ℂ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    LabelledCommonPresentation (starLanguageShape (k + 2)) (Fin 3) (2 ^ k + 3) where
  base := controlledLabelledBase k
  left := (controlledLabelledLanguage f j).left
  rightPreimage _ := controlledLabelledPreimage f hf j
  validLeft l := by
    cases l with
    | inl r =>
      have hl : (controlledLabelledLanguage f j).left (Sum.inl r) =
          qutritPinTensor (K := ℂ) r := by
        funext x
        simp [controlledLabelledLanguage, qutritPinTensor, coordinatePin]
      rw [hl, controlledLabelledLeft_eq]
      exact (controlledLeftBoolean_pin_mgi r).diskRealizable
    | inr _ =>
      change BooleanDiskRealizable (fun z => leftTransform (controlledLabelledBase k)
        qutritNeqTensor (fun i t => z (finProdFinEquiv (i,t))))
      rw [controlledLabelledLeft_eq]
      exact controlledLeftBoolean_neq_mgi.diskRealizable
  validRight _ := ((controlledBooleanPreimage_mgi f hf j).cast
    (controlledPhysicalOrder_length k)).diskRealizable


private theorem controlledLabelledPort_assignment {k : ℕ} (x : Fin (k + 2) → Fin 3)
    (p : Fin (k + 2)) :
    Sum.elim (fun l : Fin 2 => if l = 0 then x 0 else x 1)
      (fun i => x i.succ.succ) (controlledLabelledPort k p) = x p := by
  induction p using Fin.cases with
  | zero => simp [controlledLabelledPort]
  | succ p =>
    induction p using Fin.cases with
    | zero => simp [controlledLabelledPort]
    | succ p => simp [controlledLabelledPort]

/-- The cast preimage restricts to the complete ordered source tensor. -/
theorem controlledLabelledPreimage_code {k : ℕ} (f : BooleanTable k ℂ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) (x : Fin (k + 2) → Fin 3) :
    controlledLabelledPreimage f hf j
      (flattenBooleanBlocks (fun p =>
        (booleanWordEquiv (2 ^ k + 3)).symm (controlledCode k (x p)))) =
      orderedControlledQutrit f j x := by
  let r : ControlledQutritPort k → Fin 3 :=
    Sum.elim (fun l => if l = 0 then x 0 else x 1) (fun i => x i.succ.succ)
  have hr : ∀ p, r (controlledLabelledPort k p) = x p :=
    controlledLabelledPort_assignment x
  unfold controlledLabelledPreimage castBooleanTable
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
  rfl

/-- The common presentation recovers every source label exactly. -/
theorem controlledLabelledPresentation_language {k : ℕ} (f : BooleanTable k ℂ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    (controlledLabelledPresentation f hf j).language = controlledLabelledLanguage f j := by
  have hr : (controlledLabelledPresentation f hf j).language.right =
      (controlledLabelledLanguage f j).right := by
    funext l x
    change rightTransform (controlledLabelledBase k)
      (fun y => controlledLabelledPreimage f hf j (flattenBooleanBlocks y)) x =
      orderedControlledQutrit f j x
    rw [controlledLabelledBase, rightTransform_coordinateBase]
    exact controlledLabelledPreimage_code f hf j x
  have hl : (controlledLabelledPresentation f hf j).language.left =
      (controlledLabelledLanguage f j).left := rfl
  cases h : controlledLabelledLanguage f j
  cases h' : (controlledLabelledPresentation f hf j).language
  simp only [h, h'] at hl hr
  congr

/-- A concrete finite exact common width for every nowhere-zero hard table. -/
theorem controlledLabelledLanguage_hasExactCommonWidth {k : ℕ}
    (f : BooleanTable k ℂ) (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    HasExactCommonWidth (controlledLabelledLanguage f j) (2 ^ k + 3) := by
  refine ⟨Fin 3, inferInstance, inferInstance, starLanguageShape (k + 2),
    controlledLabelledPresentation f hf j, ?_⟩
  rw [controlledLabelledPresentation_language]
  exact ExactlyLabelledEquivalent.refl _

/-- In particular, the minimum exact common width is defined. -/
theorem controlledLabelledLanguage_finiteWidth {k : ℕ} (f : BooleanTable k ℂ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    ∃ r, HasExactCommonWidth (controlledLabelledLanguage f j) r :=
  ⟨2 ^ k + 3, controlledLabelledLanguage_hasExactCommonWidth f hf j⟩

end
end MatchgateWidth
