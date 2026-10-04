import MatchgateWidth.CyclePfaffian
import MatchgateWidth.MultiplicativeMobius
import MatchgateWidth.PfaffianPermutation
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Sort

/-!
# Algebraic block-Pfaffian interpolation

This file assembles the cycle components and multiplicative Möbius coefficients.
It concerns an explicitly constructed finite skew matrix only. Planar matchgate
realization is a separate obligation.
-/

namespace MatchgateWidth

open scoped BigOperators

noncomputable section

/-- A mask of consecutive pairs is equivalently a filtered finite enumeration. -/
theorem selectedPairModes_eq_finRange (n s : ℕ) (b : Fin n → Bool) :
    selectedPairModes s (List.ofFn b) =
      ((List.finRange n).filter b).flatMap
        (fun i => [s + 2 * i.val, s + 2 * i.val + 1]) := by
  induction n generalizing s with
  | zero => simp [selectedPairModes]
  | succ n ih =>
    rw [List.ofFn_succ, List.finRange_succ]
    cases hb : b 0 <;>
      simp only [hb, List.filter_cons_of_neg, List.filter_cons_of_pos,
        Bool.false_eq_true, not_false_eq_true, List.filter_map, selectedPairModes,
        List.flatMap_cons, List.flatMap_map]
    · rw [ih]
      congr 1
      funext i
      simp [Fin.val_succ, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    · rw [ih]
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, List.cons_append,
        List.nil_append]
      congr 2
      congr 1
      funext i
      simp [Fin.val_succ, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- One baseline pair for each incidence of a port in a subset. -/
abbrev PairIncidence (k : ℕ) := Σ S : Finset (Fin k), Fin S.card

/-- The two actual modes of an incidence: false is `a`, true is `b`. -/
abbrev InterpolationMode (k : ℕ) := PairIncidence k × Bool

/-- The coordinate of a mode inside its alternating-cycle component. -/
def incidenceCoordinate {k : ℕ} (m : InterpolationMode k) : ℕ :=
  2 * m.1.2.val + if m.2 then 1 else 0

/-- The explicit finite skew matrix: each subset supplies one cycle component. -/
def interpolationMatrix {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) : Matrix (InterpolationMode k) (InterpolationMode k) R :=
  fun m n => if m.1.1 = n.1.1 then
    cycleComponent m.1.1.card (y m.1.1) (incidenceCoordinate m) (incidenceCoordinate n)
    else 0

/-- All off-component entries vanish. -/
theorem interpolationMatrix_cross {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (m n : InterpolationMode k)
    (h : m.1.1 ≠ n.1.1) : interpolationMatrix y m n = 0 := by
  simp [interpolationMatrix, h]

/-- The constructed finite matrix is skew-symmetric over every commutative ring. -/
theorem interpolationMatrix_skew {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (m n : InterpolationMode k) :
    interpolationMatrix y m n = -interpolationMatrix y n m := by
  by_cases h : m.1.1 = n.1.1
  · simp only [interpolationMatrix, h, ite_true]
    exact cycleComponent_skew _ _ _ _
  · simp [interpolationMatrix, h, Ne.symm h]

@[simp] theorem interpolationMatrix_diag {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (m : InterpolationMode k) :
    interpolationMatrix y m m = 0 := by simp [interpolationMatrix]

/-- Selected whole pairs of a single component, in its increasing local order. -/
def componentModes {k : ℕ} (S : Finset (Fin k)) (b : Fin S.card → Bool) :
    List (InterpolationMode k) :=
  ((List.finRange S.card).filter b).flatMap fun j =>
    [(⟨S, j⟩, false), (⟨S, j⟩, true)]

@[simp] theorem componentModes_subset {k : ℕ} (S : Finset (Fin k))
    (b : Fin S.card → Bool) (m : InterpolationMode k) (hm : m ∈ componentModes S b) :
    m.1.1 = S := by
  simp only [componentModes, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
  obtain ⟨j, hj, rfl | rfl⟩ := hm <;> rfl

/-- Encoding the finite component gives precisely the previously verified cycle mask. -/
theorem componentModes_coordinates {k : ℕ} (S : Finset (Fin k))
    (b : Fin S.card → Bool) :
    (componentModes S b).map incidenceCoordinate = selectedPairModes 0 (List.ofFn b) := by
  rw [selectedPairModes_eq_finRange]
  simp [componentModes, List.map_flatMap, incidenceCoordinate]

/-- The actual finite matrix's component Pfaffian has the exact two-valued law. -/
theorem interpolationMatrix_component_pfaffian {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (S : Finset (Fin k)) (b : Fin S.card → Bool)
    (hS : S.Nonempty) :
    pfaffianList (interpolationMatrix y) (componentModes S b) =
      if (List.ofFn b).all id then y S else 1 := by
  rw [pfaffianList_congr (interpolationMatrix y)
    (fun m n => cycleComponent S.card (y S) (incidenceCoordinate m) (incidenceCoordinate n))
    (componentModes S b)]
  · rw [← pfaffianList_map, componentModes_coordinates]
    have hne : List.ofFn b ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at hlen
      exact (Finset.card_pos.mpr hS).ne' hlen
    simpa using cycleComponent_pfaffian_selected_pairs (List.ofFn b) (y S) hne
  · intro m hm n hn
    simp [interpolationMatrix, componentModes_subset S b m hm,
      componentModes_subset S b n hn]

/-- Increasing logical port associated with an incidence pair. -/
def incidencePort {k : ℕ} (p : PairIncidence k) : Fin k :=
  p.1.orderEmbOfFin rfl p.2

/-- Whole logical blocks induce this selection mask in each subset component. -/
def componentMask {k : ℕ} (S T : Finset (Fin k)) : Fin S.card → Bool :=
  fun j => decide (S.orderEmbOfFin rfl j ∈ T)

theorem componentMask_all {k : ℕ} (S T : Finset (Fin k)) :
    (List.ofFn (componentMask S T)).all id = true ↔ S ⊆ T := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    let j := (S.orderIsoOfFin rfl).symm ⟨i, hi⟩
    have hj : S.orderEmbOfFin rfl j = i := by
      exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
    have hv := h (componentMask S T j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
    simpa [componentMask, hj] using hv
  · intro h x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    simpa [componentMask] using h (S.orderEmbOfFin_mem rfl j)

/-- Block factorization proved from the actual entries of the assembled matrix. -/
theorem interpolationMatrix_components_pfaffian {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (Ss : List (Finset (Fin k))) (T : Finset (Fin k))
    (hdup : Ss.Nodup) (hne : ∀ S ∈ Ss, S.Nonempty) :
    pfaffianList (interpolationMatrix y)
      (Ss.flatMap fun S => componentModes S (componentMask S T)) =
      (Ss.map fun S => if S ⊆ T then y S else 1).prod := by
  induction Ss with
  | nil => simp
  | cons S Ss ih =>
    have hnot := (List.nodup_cons.mp hdup).1
    have htail := (List.nodup_cons.mp hdup).2
    simp only [List.flatMap_cons, List.map_cons, List.prod_cons]
    rw [pfaffianList_append]
    · rw [interpolationMatrix_component_pfaffian y S _ (hne S (by simp)),
        ih htail (fun U hU => hne U (by simp [hU]))]
      simp only [componentMask_all]
    · intro m hm n hn
      obtain ⟨U, hU, hn⟩ := List.mem_flatMap.mp hn
      apply interpolationMatrix_cross
      rw [componentModes_subset S _ m hm, componentModes_subset U _ n hn]
      intro h
      exact hnot (h ▸ hU)

/-- All nonempty subset components, with an arbitrary fixed enumeration. -/
def componentMajorModes {k : ℕ} (T : Finset (Fin k)) : List (InterpolationMode k) :=
  (nonemptySubsets (Finset.univ : Finset (Fin k))).toList.flatMap
    fun S => componentModes S (componentMask S T)

/-- The assembled finite matrix realizes the nonempty-subset product exactly. -/
theorem interpolationMatrix_componentMajor_pfaffian {k : ℕ} {R : Type*} [CommRing R]
    (y : Finset (Fin k) → R) (T : Finset (Fin k)) :
    pfaffianList (interpolationMatrix y) (componentMajorModes T) =
      ∏ S ∈ nonemptySubsets T, y S := by
  rw [componentMajorModes, interpolationMatrix_components_pfaffian y _ T
    (Finset.nodup_toList _)]
  · rw [← List.prod_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset,
      ← Finset.prod_filter]
    congr 1
    ext S
    simp only [Finset.mem_filter, mem_nonemptySubsets, Finset.subset_univ,
      and_true]
  · intro S hS
    have h := (mem_nonemptySubsets.mp (Finset.mem_toList.mp hS)).1
    exact Finset.nonempty_iff_ne_empty.mpr h

/-- The coefficients are constructed from `f`, so interpolation is unconditional
apart from the stated nonvanishing hypothesis. -/
def tableInterpolationMatrix {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) :
    Matrix (InterpolationMode k) (InterpolationMode k) K :=
  interpolationMatrix (nonzeroMultiplicativeMobius f hf)

/-- Algebraic interpolation in component-major order, including the empty input. -/
theorem tableInterpolationMatrix_componentMajor {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) (T : Finset (Fin k)) :
    pfaffianList (tableInterpolationMatrix f hf) (componentMajorModes T) = f T / f ∅ := by
  exact (interpolationMatrix_componentMajor_pfaffian _ T).trans
    (prod_nonzeroMultiplicativeMobius f hf T)

end

end MatchgateWidth
