import MatchgateWidth.BooleanMinors
import MatchgateWidth.TensorNetwork
import Mathlib.Tactic

/-!
# Coordinate-defined controlled qutrit tensor

This is the coordinate and linear-support layer of Propositions 8.1 and 8.2.
The two link ports precede the ordered hard ports. Hard labels are embedded as
`0,2`; the links are diagonal in `0,1`. No equality with a Pfaffian-realized
source tensor is assumed or asserted in this file.
-/

namespace MatchgateWidth
noncomputable section
open scoped Classical

variable {K : Type*} [Field K]

/-- The qutrit coordinate plane missing the indicated basis vector. -/
def qutritCoordinatePlane (r : Fin 3) : Submodule K (Fin 3 → K) :=
  LinearMap.ker (LinearMap.proj r)

@[simp] theorem mem_qutritCoordinatePlane (r : Fin 3) (v : Fin 3 → K) :
    v ∈ qutritCoordinatePlane r ↔ v r = 0 := Iff.rfl

/-- Every coordinate plane has dimension two. -/
theorem finrank_qutritCoordinatePlane (r : Fin 3) :
    Module.finrank K (qutritCoordinatePlane (K := K) r) = 2 := by
  have hs : Function.Surjective (LinearMap.proj r : (Fin 3 → K) →ₗ[K] K) :=
    fun x => ⟨fun _ => x, rfl⟩
  have h := (LinearMap.proj r : (Fin 3 → K) →ₗ[K] K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp [Module.finrank_self] at h
  change Module.finrank K ↥(LinearMap.proj r : (Fin 3 → K) →ₗ[K] K).ker = 2
  omega

/-- A zero row restricts the column support to the complementary plane. -/
theorem columnSupport_le_qutritCoordinatePlane {C : Type*} [Fintype C]
    (A : Matrix (Fin 3) C K) (r : Fin 3) (hz : ∀ c, A r c = 0) :
    columnSupport A ≤ qutritCoordinatePlane r := by
  rintro v ⟨u, rfl⟩
  change A.mulVec u r = 0
  simp [Matrix.mulVec, dotProduct, hz]

/-- A qutrit flattening with a zero row has rank at most two. -/
theorem rank_le_two_of_qutrit_zero_row {C : Type*} [Fintype C]
    (A : Matrix (Fin 3) C K) (r : Fin 3) (hz : ∀ c, A r c = 0) :
    A.rank ≤ 2 := by
  calc A.rank = Module.finrank K (columnSupport A) := rfl
       _ ≤ Module.finrank K (qutritCoordinatePlane (K := K) r) :=
         Submodule.finrank_mono (columnSupport_le_qutritCoordinatePlane A r hz)
       _ = 2 := finrank_qutritCoordinatePlane r

/-- Rank two and a zero row determine the exact support plane. -/
theorem columnSupport_eq_qutritCoordinatePlane {C : Type*} [Fintype C]
    (A : Matrix (Fin 3) C K) (r : Fin 3) (hz : ∀ c, A r c = 0)
    (hr : A.rank = 2) : columnSupport A = qutritCoordinatePlane r := by
  apply Submodule.eq_of_le_of_finrank_eq
    (columnSupport_le_qutritCoordinatePlane A r hz)
  change A.rank = _
  rw [hr, finrank_qutritCoordinatePlane]

/-- The link and hard coordinate planes together span the whole qutrit domain. -/
theorem qutrit_link_sup_hard_plane :
    qutritCoordinatePlane (K := K) 2 ⊔ qutritCoordinatePlane 1 = ⊤ := by
  apply top_unique
  intro v _
  apply Submodule.mem_sup.mpr
  refine ⟨![v 0, v 1, 0], ?_, ![0, 0, v 2], ?_, ?_⟩
  · simp
  · simp
  · ext i
    fin_cases i <;> simp

/-- Ordered link ports, followed by the ordered hard ports. -/
abbrev ControlledQutritPort (k : ℕ) := Fin 2 ⊕ Fin k

/-- Embed a Boolean hard state as qutrit state zero or two. -/
def hardQutritLabel (b : Fin 2) : Fin 3 := if b = 0 then 0 else 2

/-- Decode an admissible hard state. Its value at the forbidden state is unused. -/
def hardBooleanLabel (q : Fin 3) : Fin 2 := if q = 0 then 0 else 1

@[simp] theorem hardBooleanLabel_hardQutritLabel (b : Fin 2) :
    hardBooleanLabel (hardQutritLabel b) = b := by fin_cases b <;> decide

@[simp] theorem hardQutritLabel_ne_one (b : Fin 2) :
    hardQutritLabel b ≠ 1 := by fin_cases b <;> decide

/-- The control weight has values one and two on the two hard states. -/
def hardControlWeight (b : Fin 2) : K := if b = 0 then 1 else 2

/-- Complete coordinate definition, including all forbidden labels. -/
def controlledQutrit {k : ℕ} (f : BooleanTable k K) (j : Fin k)
    (a : ControlledQutritPort k → Fin 3) : K :=
  if ∀ i, a (Sum.inr i) ≠ 1 then
    if a (Sum.inl 0) = 0 ∧ a (Sum.inl 1) = 0 then
      f (fun i => hardBooleanLabel (a (Sum.inr i)))
    else if a (Sum.inl 0) = 1 ∧ a (Sum.inl 1) = 1 then
      hardControlWeight (hardBooleanLabel (a (Sum.inr j))) *
        f (fun i => hardBooleanLabel (a (Sum.inr i)))
    else 0
  else 0

/-- Fill the two links and embed all the Boolean hard labels. -/
def controlledQutritAssignment {k : ℕ} (a b : Fin 3) (x : BooleanInput k) :
    ControlledQutritPort k → Fin 3 :=
  Sum.elim (fun c => if c = 0 then a else b) (fun i => hardQutritLabel (x i))

@[simp] theorem controlledQutrit_00 {k : ℕ} (f : BooleanTable k K) (j : Fin k)
    (x : BooleanInput k) :
    controlledQutrit f j (controlledQutritAssignment 0 0 x) = f x := by
  simp [controlledQutrit, controlledQutritAssignment]

@[simp] theorem controlledQutrit_11 {k : ℕ} (f : BooleanTable k K) (j : Fin k)
    (x : BooleanInput k) :
    controlledQutrit f j (controlledQutritAssignment 1 1 x) =
      hardControlWeight (x j) * f x := by
  simp [controlledQutrit, controlledQutritAssignment]

@[simp] theorem controlledQutrit_01 {k : ℕ} (f : BooleanTable k K) (j : Fin k)
    (x : BooleanInput k) :
    controlledQutrit f j (controlledQutritAssignment 0 1 x) = 0 := by
  simp [controlledQutrit, controlledQutritAssignment]

@[simp] theorem controlledQutrit_10 {k : ℕ} (f : BooleanTable k K) (j : Fin k)
    (x : BooleanInput k) :
    controlledQutrit f j (controlledQutritAssignment 1 0 x) = 0 := by
  simp [controlledQutrit, controlledQutritAssignment]

/-- A hard port has no row with label one. -/
theorem controlledQutrit_hard_zero_row {k : ℕ} (f : BooleanTable k K)
    (j i : Fin k) (a : {p : ControlledQutritPort k // p ≠ Sum.inr i} → Fin 3) :
    portFlatten (controlledQutrit f j) (Sum.inr i) 1 a = 0 := by
  simp only [portFlatten, controlledQutrit]
  have h : ¬ ∀ h, insertBoundaryCoordinate (Sum.inr i) (1 : Fin 3) a (Sum.inr h) ≠ 1 := by
    intro hh
    exact hh i (by simp)
  simp [h]

/-- A link port has no row with label two. -/
theorem controlledQutrit_link_zero_row {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (l : Fin 2)
    (a : {p : ControlledQutritPort k // p ≠ Sum.inl l} → Fin 3) :
    portFlatten (controlledQutrit f j) (Sum.inl l) 2 a = 0 := by
  fin_cases l <;> simp [portFlatten, controlledQutrit]


/-- Columns exposing the two link states while fixing all hard states to zero. -/
def controlledQutritLinkColumn {k : ℕ} (l : Fin 2) (c : Fin 3) :
    {p : ControlledQutritPort k // p ≠ Sum.inl l} → Fin 3 :=
  fun p => controlledQutritAssignment (k := k) c c (fun _ => 0) p.val

/-- Both links have the explicit nonzero diagonal minor. -/
theorem controlledQutrit_link_minor {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (l : Fin 2) :
    ((portFlatten (controlledQutrit f j) (Sum.inl l)).submatrix
      ![0, 1] ![controlledQutritLinkColumn l 0, controlledQutritLinkColumn l 1]).det =
      (f (fun _ => 0)) ^ 2 := by
  fin_cases l <;>
    simp [Matrix.det_fin_two, Matrix.submatrix, portFlatten, controlledQutrit,
      controlledQutritLinkColumn, controlledQutritAssignment, insertBoundaryCoordinate,
      hardQutritLabel, hardBooleanLabel, hardControlWeight, pow_two]

/-- Each of the two actual link flattenings has rank exactly two. -/
theorem controlledQutrit_link_rank {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (hf : f (fun _ => 0) ≠ 0) (l : Fin 2) :
    (portFlatten (controlledQutrit f j) (Sum.inl l)).rank = 2 := by
  apply le_antisymm
  · exact rank_le_two_of_qutrit_zero_row _ 2 (controlledQutrit_link_zero_row f j l)
  · have hminor := controlledQutrit_link_minor f j l
    have hn : ((portFlatten (controlledQutrit f j) (Sum.inl l)).submatrix
        ![0, 1] ![controlledQutritLinkColumn l 0, controlledQutritLinkColumn l 1]).det ≠ 0 := by
      rw [hminor]
      exact pow_ne_zero _ hf
    have hl := Matrix.rank_submatrix_le (portFlatten (controlledQutrit f j) (Sum.inl l))
      ![0, 1] ![controlledQutritLinkColumn l 0, controlledQutritLinkColumn l 1]
    rw [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin] at hl
    exact hl

/-- Changing only the inserted Boolean value does not change the other coordinates. -/
theorem insertPort_eq_at_ne {k : ℕ} (i h : Fin k) (b c : Fin 2)
    (u : BooleanInput (k - 1)) (hhi : h ≠ i) :
    insertPort i b u h = insertPort i c u h := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    rcases lt_or_gt_of_ne hhi with hh | hh
    · simp [insertPort, Fin.insertNth_apply_below hh]
    · simp [insertPort, Fin.insertNth_apply_above hh]

/-- Embed a Boolean flattening column with both links fixed to zero. -/
def controlledQutritHardColumn {k : ℕ} (i : Fin k) (u : BooleanInput (k - 1)) :
    {p : ControlledQutritPort k // p ≠ Sum.inr i} → Fin 3 :=
  fun p => controlledQutritAssignment 0 0 (insertPort i 0 u) p

/-- Inserting the hard row reconstructs the ordered Boolean flattening coordinate. -/
theorem controlledQutrit_insert_hard {k : ℕ} (i : Fin k) (b : Fin 2)
    (u : BooleanInput (k - 1)) :
    insertBoundaryCoordinate (Sum.inr i) (hardQutritLabel b)
      (controlledQutritHardColumn i u) =
        controlledQutritAssignment 0 0 (insertPort i b u) := by
  ext p
  cases p with
  | inl l => simp [controlledQutritHardColumn, controlledQutritAssignment,
      insertBoundaryCoordinate]
  | inr h =>
    by_cases hh : h = i
    · subst h
      simp [controlledQutritAssignment]
    · simp [insertBoundaryCoordinate, controlledQutritHardColumn,
        controlledQutritAssignment, hh, insertPort_eq_at_ne i h 0 b u hh]

/-- The original Boolean flattening is an actual submatrix of the hard flattening. -/
theorem controlledQutrit_hard_submatrix {k : ℕ} (f : BooleanTable k K)
    (j i : Fin k) :
    (portFlatten (controlledQutrit f j) (Sum.inr i)).submatrix
      hardQutritLabel (controlledQutritHardColumn i) = oneVsRestFlattening f i := by
  ext b u
  change controlledQutrit f j (insertBoundaryCoordinate _ _ _) = _
  rw [controlledQutrit_insert_hard, controlledQutrit_00]
  rfl

/-- Each hard-port flattening inherits full Boolean rank two. -/
theorem controlledQutrit_hard_rank {k : ℕ} (f : BooleanTable k K)
    (j i : Fin k) (hf : (oneVsRestFlattening f i).rank = 2) :
    (portFlatten (controlledQutrit f j) (Sum.inr i)).rank = 2 := by
  apply le_antisymm
  · exact rank_le_two_of_qutrit_zero_row _ 1 (controlledQutrit_hard_zero_row f j i)
  · have hl := Matrix.rank_submatrix_le (portFlatten (controlledQutrit f j) (Sum.inr i))
      hardQutritLabel (controlledQutritHardColumn i)
    simpa [controlledQutrit_hard_submatrix, hf] using hl


/-- Exact link support: the span of qutrit basis states zero and one. -/
theorem controlledQutrit_link_support {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (hf : f (fun _ => 0) ≠ 0) (l : Fin 2) :
    columnSupport (portFlatten (controlledQutrit f j) (Sum.inl l)) =
      qutritCoordinatePlane 2 :=
  columnSupport_eq_qutritCoordinatePlane _ 2 (controlledQutrit_link_zero_row f j l)
    (controlledQutrit_link_rank f j hf l)

/-- Exact hard support: the span of qutrit basis states zero and two. -/
theorem controlledQutrit_hard_support {k : ℕ} (f : BooleanTable k K)
    (j i : Fin k) (hf : (oneVsRestFlattening f i).rank = 2) :
    columnSupport (portFlatten (controlledQutrit f j) (Sum.inr i)) =
      qutritCoordinatePlane 1 :=
  columnSupport_eq_qutritCoordinatePlane _ 1 (controlledQutrit_hard_zero_row f j i)
    (controlledQutrit_hard_rank f j i hf)

/-- Every port of the coordinate-defined controlled tensor has rank two. -/
theorem controlledQutrit_all_port_ranks {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (hzero : f (fun _ => 0) ≠ 0)
    (hrank : ∀ i, (oneVsRestFlattening f i).rank = 2)
    (p : ControlledQutritPort k) :
    (portFlatten (controlledQutrit f j) p).rank = 2 := by
  cases p with
  | inl l => exact controlledQutrit_link_rank f j hzero l
  | inr i => exact controlledQutrit_hard_rank f j i (hrank i)

/-- Two mode supports already span the entire right qutrit domain. -/
theorem controlledQutrit_two_supports_span {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (hzero : f (fun _ => 0) ≠ 0)
    (hrank : (oneVsRestFlattening f j).rank = 2) :
    columnSupport (portFlatten (controlledQutrit f j) (Sum.inl 0)) ⊔
      columnSupport (portFlatten (controlledQutrit f j) (Sum.inr j)) = ⊤ := by
  rw [controlledQutrit_link_support f j hzero 0,
    controlledQutrit_hard_support f j j hrank, qutrit_link_sup_hard_plane]

/-- Right support-essentiality: the sum of all mode supports is the full domain. -/
theorem controlledQutrit_support_essential {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (hzero : f (fun _ => 0) ≠ 0)
    (hrank : (oneVsRestFlattening f j).rank = 2) :
    (⨆ p : ControlledQutritPort k,
      columnSupport (portFlatten (controlledQutrit f j) p)) = ⊤ := by
  apply top_unique
  rw [← controlledQutrit_two_supports_span f j hzero hrank]
  exact sup_le (le_iSup (fun p => columnSupport (portFlatten (controlledQutrit f j) p))
      (Sum.inl 0))
    (le_iSup (fun p => columnSupport (portFlatten (controlledQutrit f j) p)) (Sum.inr j))

/-- The complete coordinate/support part of Proposition 8.2, with its Boolean
inputs explicit. The Pfaffian realization and global matchgate-width bounds
are separate obligations. -/
theorem controlledQutrit_rank_and_support_essential {k : ℕ} (f : BooleanTable k K)
    (j : Fin k) (hzero : ∀ x, f x ≠ 0)
    (hrank : ∀ i, (oneVsRestFlattening f i).rank = 2) :
    (∀ p : ControlledQutritPort k, (portFlatten (controlledQutrit f j) p).rank = 2) ∧
      (⨆ p : ControlledQutritPort k,
        columnSupport (portFlatten (controlledQutrit f j) p)) = ⊤ :=
  ⟨controlledQutrit_all_port_ranks f j (hzero _) hrank,
    controlledQutrit_support_essential f j (hzero _) (hrank j)⟩

/-- Unary qutrit pins, as actual one-port tensors. -/
def qutritPinTensor (r : Fin 3) (a : Fin 1 → Fin 3) : K :=
  if a 0 = r then 1 else 0

/-- The coordinate basis vector belongs to the corresponding pin's mode support. -/
theorem qutritPin_basis_mem_support (r : Fin 3) :
    Pi.single r (1 : K) ∈ columnSupport (portFlatten (qutritPinTensor r) 0) := by
  refine ⟨fun _ => 1, ?_⟩
  ext d
  simp [Matrix.mulVec, dotProduct,
    portFlatten, qutritPinTensor, Pi.single_apply]

/-- The three left pins are support-essential in the full qutrit dual domain.
Coordinates identify the dual with three scalars using the ordinary bilinear
pairing; no complex conjugation is involved. -/
theorem qutritPins_support_essential :
    (⨆ r : Fin 3, columnSupport (portFlatten (qutritPinTensor (K := K) r) 0)) = ⊤ := by
  apply top_unique
  intro v _
  have h : v = ∑ r : Fin 3, v r • Pi.single r (1 : K) := by
    ext d
    simp [Pi.single_apply, Finset.sum_apply]
  rw [h]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _ ((le_iSup
    (fun r => columnSupport (portFlatten (qutritPinTensor (K := K) r) 0)) r)
      (qutritPin_basis_mem_support r))


/-- A pin's support is precisely its one-dimensional coordinate line. -/
theorem qutritPin_support (r : Fin 3) :
    columnSupport (portFlatten (qutritPinTensor (K := K) r) 0) =
      K ∙ Pi.single r (1 : K) := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨∑ a, u a, ?_⟩
    ext d
    by_cases hd : d = r <;>
      simp [Matrix.mulVec, dotProduct, portFlatten, qutritPinTensor, hd]
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl : v = Pi.single r (1 : K) := Set.mem_singleton_iff.mp hv
    exact qutritPin_basis_mem_support r

/-- Every pin has port rank one. -/
theorem qutritPin_rank (r : Fin 3) :
    (portFlatten (qutritPinTensor (K := K) r) 0).rank = 1 := by
  calc (portFlatten (qutritPinTensor (K := K) r) 0).rank =
      Module.finrank K (columnSupport (portFlatten (qutritPinTensor (K := K) r) 0)) := rfl
    _ = Module.finrank K (K ∙ Pi.single r (1 : K)) := by rw [qutritPin_support]
    _ = 1 := by
      apply finrank_span_singleton
      intro h
      have := congr_fun h r
      simp at this

/-- Binary disequality on labels zero and one, including the forbidden state two. -/
def qutritNeqTensor (a : Fin 2 → Fin 3) : K :=
  if (a 0 = 0 ∧ a 1 = 1) ∨ (a 0 = 1 ∧ a 1 = 0) then 1 else 0

/-- The disequality flattenings both have their third row zero. -/
theorem qutritNeq_zero_row (l : Fin 2) (a : {p : Fin 2 // p ≠ l} → Fin 3) :
    portFlatten (qutritNeqTensor (K := K)) l 2 a = 0 := by
  fin_cases l <;> simp [portFlatten, qutritNeqTensor]

/-- The explicit antidiagonal minor at either disequality port has determinant minus one. -/
theorem qutritNeq_minor (l : Fin 2) :
    ((portFlatten (qutritNeqTensor (K := K)) l).submatrix ![0, 1]
      ![(fun _ => 0), (fun _ => 1)]).det = -1 := by
  fin_cases l <;>
    simp [Matrix.det_fin_two, Matrix.submatrix, portFlatten, qutritNeqTensor,
      insertBoundaryCoordinate]

/-- Both disequality ports have rank two. -/
theorem qutritNeq_rank (l : Fin 2) :
    (portFlatten (qutritNeqTensor (K := K)) l).rank = 2 := by
  apply le_antisymm (rank_le_two_of_qutrit_zero_row _ 2 (qutritNeq_zero_row l))
  have hn : ((portFlatten (qutritNeqTensor (K := K)) l).submatrix ![0, 1]
      ![(fun _ => 0), (fun _ => 1)]).det ≠ 0 := by
    rw [qutritNeq_minor]
    exact neg_ne_zero.mpr one_ne_zero
  have hl := Matrix.rank_submatrix_le (portFlatten (qutritNeqTensor (K := K)) l)
    ![0, 1] ![(fun _ => 0), (fun _ => 1)]
  rw [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin] at hl
  exact hl

/-- The disequality mode supports are exactly the zero-one coordinate plane. -/
theorem qutritNeq_support (l : Fin 2) :
    columnSupport (portFlatten (qutritNeqTensor (K := K)) l) =
      qutritCoordinatePlane 2 :=
  columnSupport_eq_qutritCoordinatePlane _ 2 (qutritNeq_zero_row l) (qutritNeq_rank l)

/-- Adding disequality to the three pins preserves left support-essentiality. -/
theorem qutritPins_and_neq_support_essential :
    (⨆ r : Fin 3, columnSupport (portFlatten (qutritPinTensor (K := K) r) 0)) ⊔
      (⨆ l : Fin 2, columnSupport (portFlatten (qutritNeqTensor (K := K)) l)) = ⊤ := by
  rw [qutritPins_support_essential, top_sup_eq]

end
end MatchgateWidth
