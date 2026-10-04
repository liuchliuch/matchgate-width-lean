import MatchgateWidth.ControlledPfaffian
import MatchgateWidth.CoordinateSignatures
import MatchgateWidth.OrderedPfaffianSignature

/-!
# The five-label qutrit language in the literal identity locus

This file assembles the three pins, zero-one disequality, and the controlled
right tensor using the actual common coordinate base. Boolean positions are
explicitly enumerated in block-major order. The conclusion concerns the
algebraic matchgate identities only. A planar graph realization theorem, with
compatible external order and rational weights, is a separate bridge.
-/

namespace MatchgateWidth
noncomputable section
open scoped Classical

variable {K : Type*} [Field K] {k : ℕ}

/-- Change Boolean values from `Fin 2` to `Bool`, without reordering positions. -/
def booleanWordEquiv (w : ℕ) : BooleanInput w ≃ (Fin w → Bool) where
  toFun z i := decide (z i = 1)
  invFun y i := if y i then 1 else 0
  left_inv z := by
    funext i
    change (if decide (z i = 1) then (1 : Fin 2) else 0) = z i
    generalize z i = b
    fin_cases b <;> decide
  right_inv y := by
    funext i
    change decide ((if y i then (1 : Fin 2) else 0) = 1) = y i
    cases y i <;> rfl

/-- Row-major Boolean enumeration: all wires in block zero precede block one,
and so on. `finProdFinEquiv (p,i)` is exactly the position `w*p+i`. -/
def blockBooleanEquiv (n w : ℕ) : BooleanInput (n * w) ≃ (Fin n → Fin w → Bool) where
  toFun z p i := decide (z (finProdFinEquiv (p, i)) = 1)
  invFun y t := if y (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 then 1 else 0
  left_inv z := by
    funext t
    change (if decide (z (finProdFinEquiv (finProdFinEquiv.symm t)) = 1) then (1 : Fin 2) else 0) = z t
    rw [Equiv.apply_symm_apply]
    generalize z t = b
    fin_cases b <;> decide
  right_inv y := by
    funext p i
    simp only [Equiv.symm_apply_apply]
    cases y p i <;> rfl

/-- The flattened wire position is its block offset plus its within-block index. -/
theorem blockBoolean_position_val {n w : ℕ} (p : Fin n) (i : Fin w) :
    (finProdFinEquiv (p, i)).val = w * p.val + i.val := by
  exact Nat.add_comm _ _

/-- The block-major encoding reads exactly the bit at that certified position. -/
@[simp] theorem blockBooleanEquiv_apply {n w : ℕ} (z : BooleanInput (n * w))
    (p : Fin n) (i : Fin w) :
    blockBooleanEquiv n w z p i = decide (z (finProdFinEquiv (p, i)) = 1) := rfl

/-- Coordinate pins pull back to coordinate pins through this bijective encoding. -/
theorem coordinatePin_comp_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (b : β) :
    (fun x => coordinatePin (K := K) b (e x)) = coordinatePin (e.symm b) := by
  funext x
  simp [coordinatePin, ← e.eq_symm_apply]

/-- Literal Boolean transform of an `n`-ary left tensor in block-major order. -/
def controlledLeftBoolean (n : ℕ) (F : (Fin n → Fin 3) → K) :
    BooleanTable (n * (2 ^ k + 3)) K :=
  fun z => leftTransform (controlledCoordinateBase k) F
    (blockBooleanEquiv n (2 ^ k + 3) z)

/-- A unary qutrit pin is the corresponding tensor coordinate pin. -/
theorem qutritPinTensor_eq_coordinatePin (r : Fin 3) :
    qutritPinTensor (K := K) r = coordinatePin (fun _ : Fin 1 => r) := by
  funext a
  have h : a 0 = r ↔ a = fun _ => r := by
    constructor
    · intro ha
      funext i
      fin_cases i
      exact ha
    · intro ha
      exact congrFun ha 0
  simp [qutritPinTensor, coordinatePin, h]

/-- Exact transformed coordinates of each of the three unary pins. -/
theorem controlledLeftBoolean_pin (r : Fin 3) :
    controlledLeftBoolean (k := k) 1 (qutritPinTensor (K := K) r) =
      coordinatePin ((blockBooleanEquiv 1 (2 ^ k + 3)).symm
        (fun _ => controlledCode k r)) := by
  classical
  unfold controlledLeftBoolean controlledCoordinateBase
  rw [qutritPinTensor_eq_coordinatePin]
  have hl : leftTransform (coordinateBase (K := K) (controlledCode k))
      (coordinatePin (fun _ : Fin 1 => r)) =
      coordinatePin (fun _ : Fin 1 => controlledCode k r) := by
    convert leftTransform_coordinateBase_pin (K := K) (controlledCode k)
      (fun _ : Fin 1 => r) using 1 <;> ext x <;> simp [leftTransform, coordinatePin]
  rw [hl]
  exact coordinatePin_comp_equiv _ _

/-- All three transformed pins satisfy the actual Boolean matchgate identities. -/
theorem controlledLeftBoolean_pin_mgi (r : Fin 3) :
    BooleanMatchgateIdentities
      (controlledLeftBoolean (k := k) 1 (qutritPinTensor (K := K) r)) := by
  rw [controlledLeftBoolean_pin]
  exact coordinatePin_booleanMatchgateIdentities _

/-- The two disequality support assignments, in their fixed two-port order. -/
def qutritNeqAssignment (b : Bool) : Fin 2 → Fin 3 :=
  if b then ![1, 0] else ![0, 1]

/-- Disequality is exactly the sum of the two named coordinate pins. -/
theorem qutritNeqTensor_eq_coordinatePins :
    qutritNeqTensor (K := K) = fun a =>
      coordinatePin (qutritNeqAssignment false) a +
      coordinatePin (qutritNeqAssignment true) a := by
  funext a
  have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  rw [ha]
  generalize a 0 = b
  generalize a 1 = c
  fin_cases b <;> fin_cases c <;>
    simp [qutritNeqTensor, coordinatePin, qutritNeqAssignment, Matrix.vecCons_inj]

/-- The common-base lift is additive in the supplied tensor. -/
theorem leftTransform_add {D B P : Type*} [Fintype D] [Fintype P] [Fintype B]
    [DecidableEq P] (M : Matrix D B K) (F G : (P → D) → K) :
    leftTransform M (fun x => F x + G x) =
      fun y => leftTransform M F y + leftTransform M G y := by
  funext y
  simp [leftTransform, add_mul, Finset.sum_add_distrib]

/-- The two lifted marker words, with all other physical wires zero. -/
def controlledNeqWord (k : ℕ) (b : Bool) : BooleanInput (2 * (2 ^ k + 3)) :=
  (blockBooleanEquiv 2 (2 ^ k + 3)).symm
    (fun p => controlledCode k (qutritNeqAssignment b p))

/-- Exact coordinates of transformed `X01`: the two marker coordinate pins. -/
theorem controlledLeftBoolean_neq :
    controlledLeftBoolean (k := k) 2 (qutritNeqTensor (K := K)) =
      fun z => coordinatePin (controlledNeqWord k false) z +
        coordinatePin (controlledNeqWord k true) z := by
  classical
  unfold controlledLeftBoolean controlledCoordinateBase
  rw [qutritNeqTensor_eq_coordinatePins, leftTransform_add]
  have hl : ∀ b, leftTransform (coordinateBase (K := K) (controlledCode k))
      (coordinatePin (qutritNeqAssignment b)) =
      coordinatePin (fun p => controlledCode k (qutritNeqAssignment b p)) := by
    intro b
    convert leftTransform_coordinateBase_pin (K := K) (controlledCode k)
      (qutritNeqAssignment b) using 1 <;> ext x <;> simp [leftTransform, coordinatePin]
  simp only [hl]
  have h₀ := coordinatePin_comp_equiv (K := K) (blockBooleanEquiv 2 (2 ^ k + 3))
    (fun p => controlledCode k (qutritNeqAssignment false p))
  have h₁ := coordinatePin_comp_equiv (K := K) (blockBooleanEquiv 2 (2 ^ k + 3))
    (fun p => controlledCode k (qutritNeqAssignment true p))
  exact congrArg₂ (fun F G : BooleanTable (2 * (2 ^ k + 3)) K => fun z => F z + G z) h₀ h₁

/-- The only disagreements are the first wires of the two blocks. -/
theorem controlledNeqWord_disagreements (t : Fin (2 * (2 ^ k + 3))) :
    controlledNeqWord k false t ≠ controlledNeqWord k true t ↔
      t = finProdFinEquiv (0, (0 : Fin (2 ^ k + 3))) ∨
      t = finProdFinEquiv (1, (0 : Fin (2 ^ k + 3))) := by
  obtain ⟨⟨p, i⟩, rfl⟩ := finProdFinEquiv.surjective t
  change (if controlledCode k (qutritNeqAssignment false (finProdFinEquiv.symm
      (finProdFinEquiv (p, i))).1) (finProdFinEquiv.symm (finProdFinEquiv (p, i))).2
      then (1 : Fin 2) else 0) ≠
    (if controlledCode k (qutritNeqAssignment true (finProdFinEquiv.symm
      (finProdFinEquiv (p, i))).1) (finProdFinEquiv.symm (finProdFinEquiv (p, i))).2
      then (1 : Fin 2) else 0) ↔ _
  simp only [Equiv.symm_apply_apply]
  fin_cases p <;> by_cases hi : i = 0 <;>
    simp [qutritNeqAssignment, controlledCode, hi]

/-- The transformed disequality satisfies every literal MGI in block-major order. -/
theorem controlledLeftBoolean_neq_mgi :
    BooleanMatchgateIdentities
      (controlledLeftBoolean (k := k) 2 (qutritNeqTensor (K := K))) := by
  rw [controlledLeftBoolean_neq]
  have h := weightedCoordinatePair_booleanMatchgateIdentities_of_two_positions
    (controlledNeqWord k false) (controlledNeqWord k true) (1 : K) 1
    (finProdFinEquiv (0, (0 : Fin (2 ^ k + 3))))
    (finProdFinEquiv (1, (0 : Fin (2 ^ k + 3))))
    (by simp) controlledNeqWord_disagreements
  simpa only [one_mul] using h

/-- The right preimage is encoded by positions of the certified physical list. -/
def controlledBooleanPreimage (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) : BooleanTable (controlledPhysicalOrder k).length K :=
  fun z => controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j
    (fun p i => orderedBooleanAssignment (controlledPhysicalOrder k)
      (controlledPhysicalOrder_nodup k) mem_controlledPhysicalOrder z (p, i))

/-- The constructed right preimage satisfies every literal Boolean MGI in the
certified marker/selectors/controls block-major order. -/
theorem controlledBooleanPreimage_mgi (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    BooleanMatchgateIdentities (controlledBooleanPreimage f hf j) := by
  exact orderedPfaffianSignature_booleanMatchgateIdentities
    (controlledPhysicalOrder k) (controlledPhysicalOrder_nodup k)
    mem_controlledPhysicalOrder
    (controlledPhysicalMatrix (booleanSubsetTable f) (fun _ => hf _) j)
    (controlledPhysicalMatrix_skew _ _ _) (controlledPhysicalMatrix_diag _ _ _)
    (booleanSubsetTable f ∅)

/-- Positional enumeration has precisely the full physical arity. -/
theorem controlledPhysicalOrder_length (k : ℕ) :
    (controlledPhysicalOrder k).length = (k + 2) * (2 ^ k + 3) := by
  calc
    (controlledPhysicalOrder k).length =
        Fintype.card (Fin (controlledPhysicalOrder k).length) := (Fintype.card_fin _).symm
    _ = Fintype.card (ControlledPhysicalMode k) := Fintype.card_congr
      (orderedListEquiv (controlledPhysicalOrder k) (controlledPhysicalOrder_nodup k)
        mem_controlledPhysicalOrder)
    _ = (k + 2) * (2 ^ k + 3) := controlledPhysicalMode_card k

/-- Exact coordinates of the positional preimage at all codeword assignments. -/
theorem controlledBooleanPreimage_code (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) (r : ControlledQutritPort k → Fin 3) :
    controlledBooleanPreimage f hf j
      ((orderedBooleanAssignment (controlledPhysicalOrder k)
        (controlledPhysicalOrder_nodup k) mem_controlledPhysicalOrder).symm
          (fun m => controlledCode k (r m.1) m.2)) = controlledQutrit f j r := by
  unfold controlledBooleanPreimage
  simp only [Equiv.apply_symm_apply]
  change controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j
    (fun p => controlledCode k (r p)) = _
  have h := congrFun (controlledPfaffianRestriction_eq_controlledQutrit
    (booleanSubsetTable f) (fun _ => hf _) j) r
  exact (controlledPhysicalSignature_code (booleanSubsetTable f) (fun _ => hf _) j r).trans
    (by simpa only [subsetBooleanTable_booleanSubsetTable] using h)

/-- Exactly the three left pins, left disequality, and one controlled right label. -/
inductive ControlledLanguageLabel
  | pin : Fin 3 → ControlledLanguageLabel
  | neq : ControlledLanguageLabel
  | controlled : ControlledLanguageLabel
  deriving DecidableEq, Fintype

@[simp] theorem controlledLanguageLabel_card : Fintype.card ControlledLanguageLabel = 5 := by
  decide

/-- Primitive port sets retain the intended order and semantic names. -/
abbrev controlledLanguagePorts (k : ℕ) : ControlledLanguageLabel → Type
  | .pin _ => Fin 1
  | .neq => Fin 2
  | .controlled => ControlledQutritPort k

instance (l : ControlledLanguageLabel) : Fintype (controlledLanguagePorts k l) := by
  cases l <;> dsimp [controlledLanguagePorts] <;> infer_instance

instance (l : ControlledLanguageLabel) : DecidableEq (controlledLanguagePorts k l) := by
  cases l <;> dsimp [controlledLanguagePorts] <;> infer_instance

/-- The actual five primitive qutrit tensors, including their zero coordinates. -/
def controlledLanguageTensor (f : BooleanTable k K) (j : Fin k) :
    (l : ControlledLanguageLabel) → (controlledLanguagePorts k l → Fin 3) → K
  | .pin r => qutritPinTensor r
  | .neq => qutritNeqTensor
  | .controlled => controlledQutrit f j

/-- Boolean arities include every wire and every padding mode. -/
def controlledLanguageBooleanArity (k : ℕ) : ControlledLanguageLabel → ℕ
  | .pin _ => 1 * (2 ^ k + 3)
  | .neq => 2 * (2 ^ k + 3)
  | .controlled => (controlledPhysicalOrder k).length

/-- The four actual left transforms and the actual right preimage. -/
def controlledLanguageBoolean (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) : (l : ControlledLanguageLabel) →
      BooleanTable (controlledLanguageBooleanArity k l) K
  | .pin r => controlledLeftBoolean 1 (qutritPinTensor r)
  | .neq => controlledLeftBoolean 2 qutritNeqTensor
  | .controlled => controlledBooleanPreimage f hf j

/-- Every one of the five actual Boolean components lies in the literal
identity locus. No component's identities are assumed as a premise. -/
theorem controlledLanguageBoolean_mgi (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) (l : ControlledLanguageLabel) :
    BooleanMatchgateIdentities (controlledLanguageBoolean f hf j l) := by
  cases l with
  | pin r => exact controlledLeftBoolean_pin_mgi r
  | neq => exact controlledLeftBoolean_neq_mgi
  | controlled => exact controlledBooleanPreimage_mgi f hf j

/-- Pins have rank one and all other primitive ports have rank two. -/
def controlledLanguagePortRank : ControlledLanguageLabel → ℕ
  | .pin _ => 1
  | .neq => 2
  | .controlled => 2

/-- Complete primitive port-rank statement, derived from the supplied Boolean
hard-table ranks and nonvanishing coordinates. -/
theorem controlledLanguageTensor_port_ranks (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k)
    (hrank : ∀ i, (oneVsRestFlattening f i).rank = 2)
    (l : ControlledLanguageLabel) (p : controlledLanguagePorts k l) :
    (portFlatten (controlledLanguageTensor f j l) p).rank = controlledLanguagePortRank l := by
  cases l with
  | pin r =>
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    exact qutritPin_rank r
  | neq => exact qutritNeq_rank p
  | controlled => exact controlledQutrit_all_port_ranks f j (hf _) hrank p

/-- Integer coordinates of the source table give integer coordinates of every
primitive tensor in the five-label qutrit language. -/
theorem controlledLanguageTensor_integer (f : BooleanTable k K)
    (hint : ∀ x, ∃ n : ℤ, f x = n) (j : Fin k)
    (l : ControlledLanguageLabel) (a : controlledLanguagePorts k l → Fin 3) :
    ∃ n : ℤ, controlledLanguageTensor f j l a = n := by
  cases l with
  | pin r =>
    change ∃ n : ℤ, (if a 0 = r then (1 : K) else 0) = n
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  | neq =>
    change ∃ n : ℤ, (if (a 0 = 0 ∧ a 1 = 1) ∨ (a 0 = 1 ∧ a 1 = 0)
      then (1 : K) else 0) = n
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  | controlled => exact controlledQutrit_integer_coordinates f hint j a

/-- Rational five-label algebraic presentation. The base, Pfaffian matrix,
preimage and all component transforms are explicit definitions over `ℚ`.
This theorem proves literal identities and exact coordinates/ranks/supports;
it does not identify that identity locus with planar-graph realizability. -/
theorem controlled_rational_five_label_identity_presentation
    (f : BooleanTable k ℚ) (hf : ∀ x, f x ≠ 0)
    (hint : ∀ x, ∃ n : ℤ, f x = n) (j : Fin k)
    (hrank : ∀ i, (oneVsRestFlattening f i).rank = 2) :
    Fintype.card ControlledLanguageLabel = 5 ∧
    (controlledCoordinateBase (K := ℚ) k).rank = 3 ∧
    (controlledPhysicalOrder k).length = (k + 2) * (2 ^ k + 3) ∧
    (∀ l, BooleanMatchgateIdentities (controlledLanguageBoolean f hf j l)) ∧
    rightTransform (controlledCoordinateBase k)
      (controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j) =
        controlledQutrit f j ∧
    (∀ l p, (portFlatten (controlledLanguageTensor f j l) p).rank =
      controlledLanguagePortRank l) ∧
    (∀ l a, ∃ n : ℤ, controlledLanguageTensor f j l a = n) ∧
    ((⨆ r : Fin 3, columnSupport (portFlatten (qutritPinTensor (K := ℚ) r) 0)) ⊔
      (⨆ l : Fin 2, columnSupport (portFlatten (qutritNeqTensor (K := ℚ)) l))) = ⊤ ∧
    (⨆ p : ControlledQutritPort k,
      columnSupport (portFlatten (controlledQutrit f j) p)) = ⊤ := by
  exact ⟨controlledLanguageLabel_card, controlledCoordinateBase_rank k,
    controlledPhysicalOrder_length k, controlledLanguageBoolean_mgi f hf j,
    controlledPhysicalSignature_boolean_rightTransform f hf j,
    controlledLanguageTensor_port_ranks f hf j hrank,
    controlledLanguageTensor_integer f hint j,
    qutritPins_and_neq_support_essential,
    controlledQutrit_support_essential f j (hf _) (hrank j)⟩

end
end MatchgateWidth
