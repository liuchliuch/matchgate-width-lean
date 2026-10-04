import MatchgateWidth.BlockInterpolationOrder
import MatchgateWidth.ControlledQutrit
import MatchgateWidth.PfaffianIsolated
import MatchgateWidth.BaseDecoder
import MatchgateWidth.CoordinateBase

/-!
# The finite controlled Pfaffian matrix

The explicit Section 8 matrix and its ordered codeword restriction. All entries
are constructed over the input field. Planar realization is a separate theorem.
-/

namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Semantic names for the actual finite Boolean modes. -/
inductive ControlledMode (k : ℕ)
  | selector : InterpolationMode k → ControlledMode k
  | marker : ControlledQutritPort k → ControlledMode k
  | control : ControlledQutritPort k → Bool → ControlledMode k
  | linkSelector : Fin 2 → Fin (2 ^ k) → ControlledMode k
  deriving DecidableEq, Fintype

namespace ControlledMode
variable {k : ℕ}

def p : ControlledMode k := marker (Sum.inl 0)
def q : ControlledMode k := marker (Sum.inl 1)
def a (i : Fin k) : ControlledMode k := control (Sum.inr i) false
def b (i : Fin k) : ControlledMode k := control (Sum.inr i) true
end ControlledMode

variable {k : ℕ} {K : Type*} [Field K]

/-- The marker/control part, with entries `pq=1`, `pa=1`, `qb=-1`, `ab=1`. -/
def controlledCoreMatrix (j : Fin k) : Matrix (ControlledMode k) (ControlledMode k) K
  | .marker (.inl l), .marker (.inl m) =>
      if l = 0 ∧ m = 1 then 1 else if l = 1 ∧ m = 0 then -1 else 0
  | .control (.inr i) s, .control (.inr h) t =>
      if i = h then if s = false ∧ t = true then 1
        else if s = true ∧ t = false then -1 else 0 else 0
  | .marker (.inl l), .control (.inr i) s =>
      if i = j then if l = 0 ∧ s = false then 1
        else if l = 1 ∧ s = true then -1 else 0 else 0
  | .control (.inr i) s, .marker (.inl l) =>
      -(if i = j then if l = 0 ∧ s = false then 1
        else if l = 1 ∧ s = true then -1 else 0 else 0)
  | _, _ => 0

/-- The actual finite augmented matrix. Its hard-selector corner is `A_f`. -/
def controlledPfaffianMatrix (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0)
    (j : Fin k) : Matrix (ControlledMode k) (ControlledMode k) K
  | .selector m, .selector n => tableInterpolationMatrix f hf m n
  | m, n => controlledCoreMatrix j m n

set_option maxRecDepth 2000 in
theorem controlledCoreMatrix_skew (j : Fin k) (m n : ControlledMode k) :
    controlledCoreMatrix (K := K) j m n = -controlledCoreMatrix j n m := by
  cases m <;> cases n
  all_goals try casesm* ControlledQutritPort _
  all_goals try casesm* Bool
  all_goals simp only [controlledCoreMatrix]
  all_goals try split_ifs
  all_goals simp_all <;> omega

@[simp] theorem controlledCoreMatrix_diag (j : Fin k) (m : ControlledMode k) :
    controlledCoreMatrix (K := K) j m m = 0 := by
  cases m with
  | selector _ => rfl
  | linkSelector _ _ => rfl
  | marker p => cases p with
    | inl l => fin_cases l <;> simp [controlledCoreMatrix]
    | inr i => rfl
  | control p s => cases p with
    | inl l => rfl
    | inr i => cases s <;> simp [controlledCoreMatrix]

theorem controlledPfaffianMatrix_skew (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (m n : ControlledMode k) :
    controlledPfaffianMatrix f hf j m n = -controlledPfaffianMatrix f hf j n m := by
  cases m <;> cases n <;> simp only [controlledPfaffianMatrix]
  all_goals first
    | exact interpolationMatrix_skew _ _ _
    | exact controlledCoreMatrix_skew (K := K) j _ _

@[simp] theorem controlledPfaffianMatrix_diag (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (m : ControlledMode k) :
    controlledPfaffianMatrix f hf j m m = 0 := by
  cases m <;> simp only [controlledPfaffianMatrix]
  all_goals first | exact interpolationMatrix_diag _ _ | exact controlledCoreMatrix_diag (K := K) j _

/-- Exact ordered selector list in each physical block. -/
def controlledSelectorBlock : ControlledQutritPort k → List (ControlledMode k)
  | .inl l => (List.finRange (2 ^ k)).map (.linkSelector l)
  | .inr i => (logicalModeBlock i).map .selector

/-- The actual physical order: marker, selectors, then first and second controls. -/
def controlledModeBlock (p : ControlledQutritPort k) : List (ControlledMode k) :=
  [.marker p] ++ controlledSelectorBlock p ++ [.control p false, .control p true]

theorem controlledSelectorBlock_length (p : ControlledQutritPort k) :
    (controlledSelectorBlock p).length = 2 ^ k := by
  cases p <;> simp [controlledSelectorBlock, logicalModeBlock_length]

theorem controlledModeBlock_length (p : ControlledQutritPort k) :
    (controlledModeBlock p).length = 2 ^ k + 3 := by
  simp [controlledModeBlock, controlledSelectorBlock_length]

/-- Modes selected by the three stated codewords, in physical block order. -/
def controlledSelectedBlock (p : ControlledQutritPort k) (r : Fin 3) :
    List (ControlledMode k) :=
  if r = 0 then [] else if r = 1 then [.marker p]
  else controlledSelectorBlock p ++ [.control p false, .control p true]

/-- Two link blocks precede the hard blocks in increasing logical order. -/
def controlledSelectedModes (r : ControlledQutritPort k → Fin 3) :
    List (ControlledMode k) :=
  controlledSelectedBlock (.inl 0) (r (.inl 0)) ++
  controlledSelectedBlock (.inl 1) (r (.inl 1)) ++
  (List.finRange k).flatMap (fun i => controlledSelectedBlock (.inr i) (r (.inr i)))

/-- The scaled, actual principal-Pfaffian restriction. -/
def controlledPfaffianRestriction (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0)
    (j : Fin k) (r : ControlledQutritPort k → Fin 3) : K :=
  f ∅ * pfaffianList (controlledPfaffianMatrix f hf j) (controlledSelectedModes r)

/-- Hard marker rows are literally zero. -/
theorem controlledPfaffianMatrix_hard_marker (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j i : Fin k) (m : ControlledMode k) :
    controlledPfaffianMatrix f hf j (.marker (.inr i)) m = 0 := by
  cases m <;> rfl

/-- Every nonmarker control in a link block is literally isolated. -/
theorem controlledPfaffianMatrix_link_control (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (l : Fin 2) (s : Bool)
    (m : ControlledMode k) :
    controlledPfaffianMatrix f hf j (.control (.inl l) s) m = 0 := by
  cases m <;> rfl

theorem controlledPfaffianRestriction_hard_forbidden (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j i : Fin k) (r : ControlledQutritPort k → Fin 3)
    (hr : r (.inr i) = 1) : controlledPfaffianRestriction f hf j r = 0 := by
  unfold controlledPfaffianRestriction
  rw [pfaffianList_eq_zero_of_isolated_mem _ (controlledPfaffianMatrix_skew f hf j)
    (.marker (.inr i)) (controlledPfaffianMatrix_hard_marker f hf j i)]
  · simp
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_finRange i, by simp [controlledSelectedBlock, hr]⟩

theorem controlledPfaffianRestriction_link_forbidden (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (l : Fin 2)
    (r : ControlledQutritPort k → Fin 3) (hr : r (.inl l) = 2) :
    controlledPfaffianRestriction f hf j r = 0 := by
  unfold controlledPfaffianRestriction
  rw [pfaffianList_eq_zero_of_isolated_mem _ (controlledPfaffianMatrix_skew f hf j)
    (.control (.inl l) false) (controlledPfaffianMatrix_link_control f hf j l false)]
  · simp
  · fin_cases l <;> simp_all [controlledSelectedModes, controlledSelectedBlock]


/-- Expand ordered two-mode chunks. -/
def controlledExpandPairs (ps : List (ControlledMode k × ControlledMode k)) :
    List (ControlledMode k) := ps.flatMap fun p => [p.1, p.2]

def controlledSelectorPairs (i : Fin k) : List (ControlledMode k × ControlledMode k) :=
  (logicalIncidenceBlock i).map fun p => (.selector (p, false), .selector (p, true))

def controlledHardPairs (i : Fin k) : List (ControlledMode k × ControlledMode k) :=
  controlledSelectorPairs i ++ [(ControlledMode.a i, ControlledMode.b i)]

def controlledControlModes (is : List (Fin k)) : List (ControlledMode k) :=
  is.flatMap fun i => [ControlledMode.a i, ControlledMode.b i]

def controlledHardModes (is : List (Fin k)) : List (ControlledMode k) :=
  is.flatMap fun i => controlledSelectorBlock (.inr i) ++
    [ControlledMode.a i, ControlledMode.b i]

@[simp] theorem controlledExpand_selectorPairs (i : Fin k) :
    controlledExpandPairs (controlledSelectorPairs i) = controlledSelectorBlock (.inr i) := by
  simp [controlledExpandPairs, controlledSelectorPairs, controlledSelectorBlock,
    logicalModeBlock, expandIncidencePairs, List.flatMap_map, List.map_flatMap]

theorem controlledHardModes_pairs (is : List (Fin k)) :
    controlledHardModes is = controlledExpandPairs (is.flatMap controlledHardPairs) := by
  simp [controlledHardModes, controlledExpandPairs, controlledHardPairs,
    List.flatMap_assoc, controlledSelectorPairs, controlledSelectorBlock,
    logicalModeBlock, expandIncidencePairs, List.flatMap_map, List.map_flatMap]

/-- All surviving hard blocks are whole pair chunks, including their controls. -/
theorem controlledHardModes_even (is : List (Fin k)) :
    (controlledHardModes is).length % 2 = 0 := by
  rw [controlledHardModes_pairs]
  suffices ∀ ps : List (ControlledMode k × ControlledMode k),
      (controlledExpandPairs ps).length = 2 * ps.length by rw [this]; omega
  intro ps
  induction ps with
  | nil => simp [controlledExpandPairs]
  | cons p ps ih => simp [controlledExpandPairs] at ih ⊢; omega

/-- Moving controls past complete selector pairs introduces sign `+1`. -/
theorem controlledHardModes_shuffle (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (pre : List (ControlledMode k))
    (is : List (Fin k)) :
    pfaffianList (controlledPfaffianMatrix f hf j) (pre ++ controlledHardModes is) =
      pfaffianList (controlledPfaffianMatrix f hf j)
        (pre ++ controlledControlModes is ++
          is.flatMap (fun i => controlledSelectorBlock (.inr i))) := by
  have hp := (List.flatMap_append_perm is controlledSelectorPairs
    (fun i => [(ControlledMode.a i, ControlledMode.b i)])).symm.trans
      (List.perm_append_comm)
  have he := pfaffianList_pairChunks_perm (controlledPfaffianMatrix f hf j)
    (controlledPfaffianMatrix_skew f hf j) hp pre []
  rw [controlledHardModes_pairs]
  simpa [controlledHardPairs, controlledExpandPairs, controlledControlModes,
    List.flatMap_assoc, controlledSelectorPairs, controlledSelectorBlock,
    logicalModeBlock, expandIncidencePairs, List.flatMap_map, List.map_flatMap,
    List.append_assoc] using he

/-- The hard selector corner retains the normalized interpolation value. -/
theorem controlledPfaffianMatrix_selectors (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (T : Finset (Fin k)) :
    pfaffianList (controlledPfaffianMatrix f hf j)
      ((blockMajorModes T).map ControlledMode.selector) = f T / f ∅ := by
  rw [pfaffianList_map]
  exact tableInterpolationMatrix_blockMajor f hf T

/-- Isolated hard control pairs each contribute exactly one. -/
theorem controlledPfaffianMatrix_controls (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (is : List (Fin k)) (hd : is.Nodup) :
    pfaffianList (controlledPfaffianMatrix f hf j) (controlledControlModes is) = 1 := by
  induction is with
  | nil => simp [controlledControlModes]
  | cons i is ih =>
    simp only [List.nodup_cons] at hd
    change pfaffianList _ ([ControlledMode.a i, ControlledMode.b i] ++ controlledControlModes is) = 1
    rw [pfaffianList_append, ih hd.2]
    · simp [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.a, ControlledMode.b]
    · intro m hm n hn
      obtain ⟨h, hh, hn⟩ := List.mem_flatMap.mp hn
      have hih : i ≠ h := fun e => hd.1 (e ▸ hh)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hn
      rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
        simp [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.a,
          ControlledMode.b, hih]

/-- The actual four distinguished entries give the value two. -/
theorem controlledPfaffianMatrix_four (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) :
    pfaffianList (controlledPfaffianMatrix f hf j)
      [ControlledMode.p, ControlledMode.q, ControlledMode.a j, ControlledMode.b j] = 2 := by
  rw [pfaffianList_four]
  norm_num [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.p,
    ControlledMode.q, ControlledMode.a, ControlledMode.b]


/-- The links see the designated selected hard control pair, and no others. -/
theorem controlledPfaffianMatrix_links_controls (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (is : List (Fin k)) (hd : is.Nodup) :
    pfaffianList (controlledPfaffianMatrix f hf j)
      ([ControlledMode.p, ControlledMode.q] ++ controlledControlModes is) =
        if j ∈ is then 2 else 1 := by
  by_cases hj : j ∈ is
  · have hp := (List.perm_cons_erase hj).map
      (fun i => (ControlledMode.a i, ControlledMode.b i))
    have he := pfaffianList_pairChunks_perm (controlledPfaffianMatrix f hf j)
      (controlledPfaffianMatrix_skew f hf j) hp [ControlledMode.p, ControlledMode.q] []
    have he' : pfaffianList (controlledPfaffianMatrix f hf j)
        ([ControlledMode.p, ControlledMode.q] ++ controlledControlModes is) =
      pfaffianList (controlledPfaffianMatrix f hf j)
        ([ControlledMode.p, ControlledMode.q, ControlledMode.a j, ControlledMode.b j] ++
          controlledControlModes (is.erase j)) := by
      simpa [controlledControlModes, List.flatMap_map] using he
    rw [he', pfaffianList_append, controlledPfaffianMatrix_four,
      controlledPfaffianMatrix_controls f hf j _ (hd.erase j), ite_eq_left hj, mul_one]
    intro m hm n hn
    obtain ⟨h, hh, hn⟩ := List.mem_flatMap.mp hn
    have hhj : h ≠ j := fun e => hd.not_mem_erase (e ▸ hh)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hn
    rcases hm with rfl | rfl | rfl | rfl <;> rcases hn with rfl | rfl <;>
      simp [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.p,
        ControlledMode.q, ControlledMode.a, ControlledMode.b, hhj, Ne.symm hhj]
  · rw [pfaffianList_append, controlledPfaffianMatrix_controls f hf j is hd,
      ite_eq_right hj, mul_one, pfaffianList_pair]
    · simp [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.p, ControlledMode.q]
    · intro m hm n hn
      obtain ⟨h, hh, hn⟩ := List.mem_flatMap.mp hn
      have hhj : h ≠ j := fun e => hj (e ▸ hh)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hn
      rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
        simp [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.p,
          ControlledMode.q, ControlledMode.a, ControlledMode.b, hhj]

/-- Ordered hard ports selected by a subset. -/
def controlledSelectedPorts (T : Finset (Fin k)) : List (Fin k) :=
  (List.finRange k).filter fun i => decide (i ∈ T)

@[simp] theorem mem_controlledSelectedPorts (T : Finset (Fin k)) (i : Fin k) :
    i ∈ controlledSelectedPorts T ↔ i ∈ T := by simp [controlledSelectedPorts]

theorem controlledSelectedPorts_nodup (T : Finset (Fin k)) :
    (controlledSelectedPorts T).Nodup := (List.nodup_finRange k).filter _

/-- The exact block shuffle separates the constructed interpolation corner. -/
theorem controlledPfaffianMatrix_factor (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (pre : List (ControlledMode k))
    (hp : ∀ m ∈ pre, ∀ n : InterpolationMode k,
      controlledPfaffianMatrix f hf j m (.selector n) = 0) (T : Finset (Fin k)) :
    pfaffianList (controlledPfaffianMatrix f hf j)
      (pre ++ controlledHardModes (controlledSelectedPorts T)) =
      pfaffianList (controlledPfaffianMatrix f hf j)
        (pre ++ controlledControlModes (controlledSelectedPorts T)) * (f T / f ∅) := by
  rw [controlledHardModes_shuffle]
  have he : (controlledSelectedPorts T).flatMap
      (fun i => controlledSelectorBlock (.inr i)) =
      (blockMajorModes T).map ControlledMode.selector := by
    simp [blockMajorModes_eq_logicalBlocks, controlledSelectedPorts,
      controlledSelectorBlock, List.map_flatMap]
  rw [he, pfaffianList_append, controlledPfaffianMatrix_selectors]
  intro m hm n hn
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hn
  rcases List.mem_append.mp hm with hm | hm
  · exact hp m hm n
  · obtain ⟨i, _, hm⟩ := List.mem_flatMap.mp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> rfl

/-- Embed a Boolean subset in the hard qutrit coordinates. -/
def controlledSubsetAssignment (l r : Fin 3) (T : Finset (Fin k)) :
    ControlledQutritPort k → Fin 3 :=
  Sum.elim (fun c => if c = 0 then l else r) (fun i => if i ∈ T then 2 else 0)

theorem controlledSelectedModes_subset (l r : Fin 3) (T : Finset (Fin k)) :
    controlledSelectedModes (controlledSubsetAssignment l r T) =
      controlledSelectedBlock (.inl 0) l ++ controlledSelectedBlock (.inl 1) r ++
        controlledHardModes (controlledSelectedPorts T) := by
  simp only [controlledSelectedModes, controlledSubsetAssignment, Sum.elim_inl,
    Sum.elim_inr, ite_true, Fin.reduceEq, ite_false]
  congr 1
  simp only [controlledHardModes, controlledSelectedPorts]
  generalize List.finRange k = is
  induction is with
  | nil => simp
  | cons i is ih =>
    by_cases hi : i ∈ T <;>
      simp_all [controlledSelectedBlock, ControlledMode.a, ControlledMode.b]

theorem controlledPfaffianRestriction_subset_00 (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (T : Finset (Fin k)) :
    controlledPfaffianRestriction f hf j (controlledSubsetAssignment 0 0 T) = f T := by
  unfold controlledPfaffianRestriction
  rw [controlledSelectedModes_subset]
  simp only [controlledSelectedBlock, Fin.reduceEq, ite_true, List.nil_append]
  have he := controlledPfaffianMatrix_factor f hf j [] (by simp) T
  simp only [List.nil_append] at he
  rw [he, controlledPfaffianMatrix_controls f hf j _ (controlledSelectedPorts_nodup T)]
  field_simp [hf ∅]

theorem controlledPfaffianRestriction_subset_11 (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (T : Finset (Fin k)) :
    controlledPfaffianRestriction f hf j (controlledSubsetAssignment 1 1 T) =
      (if j ∈ T then 2 else 1) * f T := by
  unfold controlledPfaffianRestriction
  rw [controlledSelectedModes_subset]
  simp only [controlledSelectedBlock, Fin.reduceEq, ite_false, ite_true,
    List.singleton_append]
  change f ∅ * pfaffianList _ ([ControlledMode.p, ControlledMode.q] ++ _) = _
  rw [controlledPfaffianMatrix_factor, controlledPfaffianMatrix_links_controls f hf j _
    (controlledSelectedPorts_nodup T)]
  · simp only [mem_controlledSelectedPorts]
    field_simp [hf ∅]
  · intro m hm n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> rfl

/-- A mixed link choice has odd total selected cardinality. -/
theorem controlledPfaffianRestriction_subset_mixed (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (T : Finset (Fin k))
    (l r : Fin 3) (hlr : (l = 0 ∧ r = 1) ∨ (l = 1 ∧ r = 0)) :
    controlledPfaffianRestriction f hf j (controlledSubsetAssignment l r T) = 0 := by
  unfold controlledPfaffianRestriction
  rw [controlledSelectedModes_subset]
  rw [pfaffianList_odd]
  · simp
  · have he := controlledHardModes_even (controlledSelectedPorts T)
    rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [controlledSelectedBlock] <;> omega


/-- View a subset-indexed table as the equivalent ordered Boolean table. -/
def subsetBooleanTable (f : Finset (Fin k) → K) : BooleanTable k K :=
  fun x => f (Finset.univ.filter fun i => x i = 1)

theorem controlledQutrit_subset (f : Finset (Fin k) → K) (j : Fin k)
    (l r : Fin 3) (T : Finset (Fin k)) :
    controlledQutrit (subsetBooleanTable f) j (controlledSubsetAssignment l r T) =
      if l = 0 ∧ r = 0 then f T
      else if l = 1 ∧ r = 1 then (if j ∈ T then 2 else 1) * f T else 0 := by
  have hT : Finset.univ.filter (fun i => hardBooleanLabel
      (if i ∈ T then 2 else 0) = 1) = T := by
    ext i
    by_cases hi : i ∈ T <;> simp [hardBooleanLabel, hi]
  have hh : ∀ i : Fin k, (if i ∈ T then (2 : Fin 3) else 0) ≠ 1 := by
    intro i
    split_ifs <;> decide
  have hh' : ∀ i, controlledSubsetAssignment l r T (Sum.inr i) ≠ 1 := hh
  simp only [controlledQutrit, ite_eq_left hh']
  simp only [controlledSubsetAssignment, Sum.elim_inr, Sum.elim_inl,
    Fin.reduceEq, ite_true, ite_false, subsetBooleanTable]
  by_cases hi : j ∈ T <;> simp [hardControlWeight, hardBooleanLabel, hi]

/-- The complete constructed Pfaffian restriction is the coordinate-defined tensor. -/
theorem controlledPfaffianRestriction_eq_controlledQutrit
    (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0) (j : Fin k) :
    controlledPfaffianRestriction f hf j = controlledQutrit (subsetBooleanTable f) j := by
  funext r
  by_cases hh : ∀ i, r (.inr i) ≠ 1
  · by_cases hl : ∀ l : Fin 2, r (.inl l) ≠ 2
    · let T : Finset (Fin k) := Finset.univ.filter fun i => r (.inr i) = 2
      have hr : r = controlledSubsetAssignment (r (.inl 0)) (r (.inl 1)) T := by
        funext p
        cases p with
        | inl l => fin_cases l <;> simp [controlledSubsetAssignment]
        | inr i =>
          have hi := hh i
          simp only [controlledSubsetAssignment, Sum.elim_inr, T,
            Finset.mem_filter, Finset.mem_univ, true_and]
          generalize r (Sum.inr i) = c at *
          fin_cases c <;> simp_all
      rw [hr]
      rw [controlledQutrit_subset]
      have hl0 := hl 0
      have hl1 := hl 1
      generalize r (Sum.inl 0) = c at *
      generalize r (Sum.inl 1) = d at *
      fin_cases c <;> fin_cases d <;> simp_all
      · exact controlledPfaffianRestriction_subset_00 f hf j T
      · exact controlledPfaffianRestriction_subset_mixed f hf j T 0 1 (by simp)
      · exact controlledPfaffianRestriction_subset_mixed f hf j T 1 0 (by simp)
      · simpa only [ite_mul, one_mul] using controlledPfaffianRestriction_subset_11 f hf j T
    · push Not at hl
      obtain ⟨l, hl⟩ := hl
      rw [controlledPfaffianRestriction_link_forbidden f hf j l r hl]
      fin_cases l <;> simp_all [controlledQutrit]
  · push Not at hh
    obtain ⟨i, hi⟩ := hh
    rw [controlledPfaffianRestriction_hard_forbidden f hf j i r hi]
    have hn : ¬∀ i, r (.inr i) ≠ 1 := fun h => h i hi
    simp [controlledQutrit, hn]


/-- The common block width and its Boolean words. -/
abbrev ControlledWord (k : ℕ) := Fin (2 ^ k + 3) → Bool

/-- The named Section 8 codewords, in marker/selectors/controls order. -/
def controlledCode (k : ℕ) (r : Fin 3) : ControlledWord k :=
  if r = 0 then fun _ => false
  else if r = 1 then fun i => decide (i = 0)
  else fun i => decide (i ≠ 0)

def controlledB0 (k : ℕ) : ControlledWord k := controlledCode k 0
def controlledB1 (k : ℕ) : ControlledWord k := controlledCode k 1
def controlledB2 (k : ℕ) : ControlledWord k := controlledCode k 2

theorem controlledCode_injective (k : ℕ) : Function.Injective (controlledCode k) := by
  intro r s h
  have h0 := congrFun h 0
  let oneWire : Fin (2 ^ k + 3) := ⟨1, Nat.lt_add_left (2 ^ k) (by decide : 1 < 3)⟩
  have hn : oneWire ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [oneWire] at this
  have h1 := congrFun h oneWire
  fin_cases r <;> fin_cases s <;> simp_all [controlledCode]

/-- The literal three-coordinate-row base, over the same field. -/
def controlledCoordinateBase (k : ℕ) : Matrix (Fin 3) (ControlledWord k) K :=
  coordinateBase (controlledCode k)

theorem controlledCoordinateBase_rank (k : ℕ) :
    (controlledCoordinateBase (K := K) k).rank = 3 := by
  exact coordinateBase_rank _ (controlledCode_injective k)

/-- Select the one bits of a word in the supplied finite list's exact order. -/
def controlledSelectWord {α : Type*} (xs : List α) (y : Fin xs.length → Bool) : List α :=
  ((List.finRange xs.length).filter y).map xs.get

@[simp] theorem controlledSelectWord_marker {α : Type*} (a : α) (xs : List α) :
    controlledSelectWord (a :: xs) (fun i => decide (i = 0)) = [a] := by
  simp [controlledSelectWord, List.finRange_succ, List.filter_map, Function.comp_def]

@[simp] theorem controlledSelectWord_nonmarker {α : Type*} (a : α) (xs : List α) :
    controlledSelectWord (a :: xs) (fun i => decide (i ≠ 0)) = xs := by
  simp [controlledSelectWord, List.finRange_succ, List.filter_map, Function.comp_def,
    List.map_map]

/-- The named Boolean words select exactly the stated marker/selector/control lists. -/
theorem controlledCode_selects (p : ControlledQutritPort k) (r : Fin 3) :
    controlledSelectWord (controlledModeBlock p)
      (fun i => controlledCode k r (i.cast (controlledModeBlock_length p))) =
        controlledSelectedBlock p r := by
  haveI : NeZero (controlledModeBlock p).length := ⟨by
    apply ne_of_gt
    rw [controlledModeBlock_length]
    exact Nat.lt_add_left (2 ^ k) (by decide : 0 < 3)⟩
  fin_cases r
  · simp [controlledCode, controlledSelectWord, controlledSelectedBlock]
  · change controlledSelectWord (controlledModeBlock p)
      (fun i => decide (i.cast (controlledModeBlock_length p) = 0)) = [.marker p]
    simp only [ Fin.cast_eq_zero]
    exact controlledSelectWord_marker (.marker p)
      (controlledSelectorBlock p ++ [.control p false, .control p true])
  · change controlledSelectWord (controlledModeBlock p)
      (fun i => decide (i.cast (controlledModeBlock_length p) ≠ 0)) =
        controlledSelectorBlock p ++ [.control p false, .control p true]
    simp only [ne_eq, Fin.cast_eq_zero]
    exact controlledSelectWord_nonmarker (.marker p)
      (controlledSelectorBlock p ++ [.control p false, .control p true])

/-- Actual uniform physical index type: `k+2` blocks of `2^k+3` wires. -/
abbrev ControlledPhysicalMode (k : ℕ) := ControlledQutritPort k × Fin (2 ^ k + 3)

/-- Identify a physical wire with its explicitly constructed semantic mode. -/
def controlledPhysicalWire (m : ControlledPhysicalMode k) : ControlledMode k :=
  (controlledModeBlock m.1).get (m.2.cast (controlledModeBlock_length m.1).symm)

/-- The augmented matrix on the uniform, actual physical indices. -/
def controlledPhysicalMatrix (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0)
    (j : Fin k) : Matrix (ControlledPhysicalMode k) (ControlledPhysicalMode k) K :=
  fun m n => controlledPfaffianMatrix f hf j (controlledPhysicalWire m) (controlledPhysicalWire n)

/-- Fixed external order of the blocks. -/
def controlledPortOrder (k : ℕ) : List (ControlledQutritPort k) :=
  [.inl 0, .inl 1] ++ (List.finRange k).map Sum.inr

/-- Fixed external order of wires inside one physical block. -/
def controlledPhysicalBlock (p : ControlledQutritPort k) : List (ControlledPhysicalMode k) :=
  (List.finRange (controlledModeBlock p).length).map
    (fun i => (p, i.cast (controlledModeBlock_length p)))

/-- The full physical mode order. -/
def controlledPhysicalOrder (k : ℕ) : List (ControlledPhysicalMode k) :=
  (controlledPortOrder k).flatMap controlledPhysicalBlock

/-- The scaled Boolean principal-Pfaffian signature, before qutrit restriction. -/
def controlledPhysicalSignature (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0)
    (j : Fin k) (y : ControlledQutritPort k → ControlledWord k) : K :=
  f ∅ * pfaffianList (controlledPhysicalMatrix f hf j)
    ((controlledPhysicalOrder k).filter fun m => y m.1 m.2)

/-- Codeword restriction of the genuine Boolean signature has the proved mode list. -/
theorem controlledPhysicalSignature_code (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (r : ControlledQutritPort k → Fin 3) :
    controlledPhysicalSignature f hf j (fun p => controlledCode k (r p)) =
      controlledPfaffianRestriction f hf j r := by
  unfold controlledPhysicalSignature controlledPhysicalMatrix
  rw [← pfaffianList_map]
  congr 1
  have hb : ∀ p : ControlledQutritPort k,
      ((controlledPhysicalBlock p).filter (fun m => controlledCode k (r m.1) m.2)).map
        controlledPhysicalWire = controlledSelectedBlock p (r p) := by
    intro p
    convert controlledCode_selects p (r p) using 1 <;>
      simp [controlledPhysicalBlock, controlledPhysicalWire, controlledSelectWord,
        List.filter_map, List.map_map, Function.comp_def]
  simp only [controlledPhysicalOrder, List.filter_flatMap, List.map_flatMap, hb]
  simp [controlledPortOrder, controlledSelectedModes, List.flatMap_map]

/-- The exact common-base contraction equals the specified qutrit tensor. -/
theorem controlledPhysicalSignature_rightTransform (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) :
    rightTransform (controlledCoordinateBase k) (controlledPhysicalSignature f hf j) =
      controlledQutrit (subsetBooleanTable f) j := by
  funext r
  rw [controlledCoordinateBase, rightTransform_coordinateBase,
    controlledPhysicalSignature_code, controlledPfaffianRestriction_eq_controlledQutrit]


/-- Exact number of physical wires, including both links and every padding mode. -/
theorem controlledPhysicalMode_card (k : ℕ) :
    Fintype.card (ControlledPhysicalMode k) = (k + 2) * (2 ^ k + 3) := by
  simp [ControlledPhysicalMode, ControlledQutritPort, Nat.add_comm]

theorem controlledPortOrder_nodup (k : ℕ) : (controlledPortOrder k).Nodup := by
  simp [controlledPortOrder]
  exact (List.nodup_finRange k).map Sum.inr_injective

@[simp] theorem mem_controlledPortOrder (p : ControlledQutritPort k) :
    p ∈ controlledPortOrder k := by
  cases p with
  | inl l => fin_cases l <;> simp [controlledPortOrder]
  | inr i => simp [controlledPortOrder]

/-- Every physical block lists each of its wire positions exactly once. -/
theorem controlledPhysicalBlock_nodup (p : ControlledQutritPort k) :
    (controlledPhysicalBlock p).Nodup := by
  apply (List.nodup_finRange _).map
  intro i j h
  exact Fin.ext (congrArg (fun m : ControlledPhysicalMode k => m.2.val) h)

/-- The physical order is a genuine exhaustive finite ordering. -/
theorem controlledPhysicalOrder_nodup (k : ℕ) : (controlledPhysicalOrder k).Nodup := by
  rw [controlledPhysicalOrder, List.nodup_flatMap]
  constructor
  · intro p _
    exact controlledPhysicalBlock_nodup p
  · apply List.Pairwise.imp _ (controlledPortOrder_nodup k)
    intro p q hpq
    apply List.disjoint_left.mpr
    intro m hm hn
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hn
    exact hpq (congrArg Prod.fst (hi.trans hj.symm))

@[simp] theorem mem_controlledPhysicalOrder (m : ControlledPhysicalMode k) :
    m ∈ controlledPhysicalOrder k := by
  apply List.mem_flatMap.mpr
  refine ⟨m.1, mem_controlledPortOrder _, ?_⟩
  apply List.mem_map.mpr
  exact ⟨m.2.cast (controlledModeBlock_length m.1).symm,
    List.mem_finRange _, by simp⟩

theorem controlledPhysicalMatrix_skew (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (m n : ControlledPhysicalMode k) :
    controlledPhysicalMatrix f hf j m n = -controlledPhysicalMatrix f hf j n m :=
  controlledPfaffianMatrix_skew f hf j _ _

@[simp] theorem controlledPhysicalMatrix_diag (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) (m : ControlledPhysicalMode k) :
    controlledPhysicalMatrix f hf j m m = 0 := controlledPfaffianMatrix_diag f hf j _

/-- Full algebraic conclusion over the paper's rational field. It asserts the
actual matrix and exact contraction, not a planar-realization hypothesis. -/
theorem exists_controlled_rational_restriction (f : Finset (Fin k) → ℚ)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) :
    ∃ (A : Matrix (ControlledPhysicalMode k) (ControlledPhysicalMode k) ℚ)
      (M : Matrix (Fin 3) (ControlledWord k) ℚ) (c : ℚ),
      (∀ m n, A m n = -A n m) ∧ (∀ m, A m m = 0) ∧ M.rank = 3 ∧
      (controlledPhysicalOrder k).Nodup ∧
      (∀ m, m ∈ controlledPhysicalOrder k) ∧
      (∀ r : ControlledQutritPort k → Fin 3,
        rightTransform M (fun y => c * pfaffianList A
          ((controlledPhysicalOrder k).filter fun m => y m.1 m.2)) r =
            controlledQutrit (subsetBooleanTable f) j r) := by
  refine ⟨controlledPhysicalMatrix f hf j, controlledCoordinateBase k, f ∅,
    controlledPhysicalMatrix_skew f hf j, controlledPhysicalMatrix_diag f hf j,
    controlledCoordinateBase_rank k, controlledPhysicalOrder_nodup k,
    mem_controlledPhysicalOrder, ?_⟩
  intro r
  exact congrFun (controlledPhysicalSignature_rightTransform f hf j) r


/-- The stipulated control signs are entries of the constructed matrix. -/
theorem controlledPfaffianMatrix_control_entries (f : Finset (Fin k) → K)
    (hf : ∀ S, f S ≠ 0) (j : Fin k) :
    controlledPfaffianMatrix f hf j ControlledMode.p ControlledMode.q = 1 ∧
    controlledPfaffianMatrix f hf j ControlledMode.p (ControlledMode.a j) = 1 ∧
    controlledPfaffianMatrix f hf j ControlledMode.q (ControlledMode.b j) = -1 ∧
    controlledPfaffianMatrix f hf j (ControlledMode.a j) (ControlledMode.b j) = 1 := by
  simp [controlledPfaffianMatrix, controlledCoreMatrix, ControlledMode.p,
    ControlledMode.q, ControlledMode.a, ControlledMode.b]

/-- Reindex an ordered Boolean table by its selected subset. -/
def booleanSubsetTable (f : BooleanTable k K) (S : Finset (Fin k)) : K :=
  f (fun i => if i ∈ S then 1 else 0)

@[simp] theorem subsetBooleanTable_booleanSubsetTable (f : BooleanTable k K) :
    subsetBooleanTable (booleanSubsetTable f) = f := by
  funext x
  unfold subsetBooleanTable booleanSubsetTable
  congr 1
  funext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  generalize x i = b
  fin_cases b <;> simp

/-- Direct interface for the paper's ordered Boolean table. -/
theorem controlledPhysicalSignature_boolean_rightTransform (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    rightTransform (controlledCoordinateBase k)
      (controlledPhysicalSignature (booleanSubsetTable f) (fun S => hf _) j) =
        controlledQutrit f j := by
  simpa only [subsetBooleanTable_booleanSubsetTable] using
    controlledPhysicalSignature_rightTransform (booleanSubsetTable f) (fun _ => hf _) j

/-- Integer input coordinates give integer output coordinates after restriction. -/
theorem controlledQutrit_integer_coordinates (f : BooleanTable k K)
    (hf : ∀ x, ∃ n : ℤ, f x = n) (j : Fin k)
    (r : ControlledQutritPort k → Fin 3) :
    ∃ n : ℤ, controlledQutrit f j r = n := by
  unfold controlledQutrit
  split_ifs
  · exact hf _
  · obtain ⟨n, hn⟩ := hf (fun i => hardBooleanLabel (r (.inr i)))
    rw [hn]
    unfold hardControlWeight
    split_ifs
    · exact ⟨n, by simp⟩
    · exact ⟨2 * n, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

/-- In particular the rational presentation has integer-valued qutrit restriction
whenever the initial table does. -/
theorem controlledPhysicalSignature_integer_restriction (f : BooleanTable k ℚ)
    (hf : ∀ x, f x ≠ 0) (hint : ∀ x, ∃ n : ℤ, f x = n) (j : Fin k)
    (r : ControlledQutritPort k → Fin 3) :
    ∃ n : ℤ, rightTransform (controlledCoordinateBase k)
      (controlledPhysicalSignature (booleanSubsetTable f) (fun S => hf _) j) r = n := by
  rw [controlledPhysicalSignature_boolean_rightTransform]
  exact controlledQutrit_integer_coordinates f hint j r

end
end MatchgateWidth
