import MatchgateWidth.MatchingSignature

/-!
# The finite signed crossover gadget

This file checks the seven-edge graph in Figure 6 of Cai--Gorenstein,
*Matchgates Revisited*, Theory of Computing 10 (2014), 167--197,
DOI 10.4086/toc.2014.v010a007. The four external vertices are numbered
clockwise, starting at the upper left. The checked table is (5.3)--(5.6).

Only the finite weighted matching calculation is asserted here. The drawing
coordinates below are data, not a formal proof of planarity or outer-face order.
-/

namespace MatchgateWidth

/-- Left endpoints of the six cycle edges followed by the negative chord. -/
def crossoverLeft : Fin 7 → Fin 6 := ![0, 1, 5, 2, 3, 4, 4]

/-- Right endpoints, in the same edge order. -/
def crossoverRight : Fin 7 → Fin 6 := ![1, 5, 2, 3, 4, 0, 5]

/-- The explicit signed six-vertex gadget, with its seventh edge negative. -/
def crossoverGraph : WeightedGraph (Fin 6) (Fin 7) ℤ where
  left := crossoverLeft
  right := crossoverRight
  loopless := by decide
  weight := ![1, 1, 1, 1, 1, 1, -1]

/-- External vertices in clockwise order in the displayed rectangular drawing. -/
def crossoverExternal : Fin 4 → Fin 6 := ![0, 1, 2, 3]

/-- Drawing data only: these coordinates do not package a planarity theorem. -/
def crossoverDrawing : Fin 6 → ℤ × ℤ :=
  ![(0, 2), (2, 2), (2, 0), (0, 0), (0, 1), (2, 1)]

/-- A computable version of the same degree calculation. -/
def crossoverDegree (m : Finset (Fin 7)) (v : Fin 6) : ℕ :=
  ∑ e ∈ m, ((if crossoverLeft e = v then 1 else 0) +
    (if crossoverRight e = v then 1 else 0))

/-- A computable version of the same active-vertex calculation. -/
def crossoverActive (x : Fin 4 → Bool) : Finset (Fin 6) :=
  Finset.univ.filter (fun v => ¬ ∃ i, x i = true ∧ crossoverExternal i = v)

/-- This sum enumerates actual edge subsets and tests the perfect matching condition. -/
def crossoverSum (x : Fin 4 → Bool) : ℤ :=
  ∑ m : Finset (Fin 7),
    if (∀ v : Fin 6, crossoverDegree m v = if v ∈ crossoverActive x then 1 else 0)
    then ∏ e ∈ m, crossoverGraph.weight e else 0

theorem crossoverSum_eq_deletionSignature (x : Fin 4 → Bool) :
    crossoverSum x = deletionSignature crossoverGraph crossoverExternal x := by
  classical
  unfold crossoverSum deletionSignature weightedPerfectMatch
  apply Finset.sum_congr rfl
  intro m _
  have hdeg : ∀ v, crossoverDegree m v = matchingDegree crossoverGraph m v := by
    intro v
    unfold crossoverDegree matchingDegree
    apply Finset.sum_congr rfl
    intro e _
    apply congrArg₂ (· + ·) <;> apply (ite_eq_ite _ _ _).mpr trivial
  have hactive : crossoverActive x = deletionActive crossoverExternal x := by
    ext v
    simp [crossoverActive, deletionActive]
  have hm : (∀ v : Fin 6,
      crossoverDegree m v = if v ∈ crossoverActive x then 1 else 0) ↔
      MatchesExactly crossoverGraph (deletionActive crossoverExternal x) m := by
    constructor <;> intro h v
    all_goals
      have hv := h v
      by_cases ha : v ∈ crossoverActive x
      · have hb : v ∈ deletionActive crossoverExternal x := hactive ▸ ha
        simpa only [hdeg, ha, hb, ↓reduceIte] using hv
      · have hb : v ∉ deletionActive crossoverExternal x := hactive ▸ ha
        simpa only [hdeg, ha, hb, ↓reduceIte] using hv
  by_cases h : ∀ v : Fin 6,
      crossoverDegree m v = if v ∈ crossoverActive x then 1 else 0
  · rw [ite_eq_left h, ite_eq_left (hm.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hm.mpr hc))]

/-- Expected signed crossing tensor in deletion coordinates. -/
def signedCrossoverValue (x : Fin 4 → Bool) : ℤ :=
  if x 0 = x 2 ∧ x 1 = x 3 then
    if x 0 = true ∧ x 1 = true then -1 else 1
  else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All sixteen entries are verified by the kernel's finite evaluation. -/
theorem crossoverSum_table : ∀ x : Fin 4 → Bool,
    crossoverSum x = signedCrossoverValue x := by
  decide

/-- The actual finite weighted matching signature is the signed crossing tensor. -/
theorem crossover_deletionSignature (x : Fin 4 → Bool) :
    deletionSignature crossoverGraph crossoverExternal x = signedCrossoverValue x := by
  rw [← crossoverSum_eq_deletionSignature]
  exact crossoverSum_table x

/-- The same concrete graph over any commutative ring. -/
def crossoverGraphOver (K : Type*) [CommRing K] : WeightedGraph (Fin 6) (Fin 7) K where
  left := crossoverLeft
  right := crossoverRight
  loopless := crossoverGraph.loopless
  weight := fun e => (crossoverGraph.weight e : K)

/-- Changing coefficients by the integer cast commutes with this matching sum. -/
theorem crossover_deletionSignature_cast {K : Type*} [CommRing K]
    (x : Fin 4 → Bool) :
    deletionSignature (crossoverGraphOver K) crossoverExternal x =
      ((deletionSignature crossoverGraph crossoverExternal x : ℤ) : K) := by
  classical
  unfold deletionSignature weightedPerfectMatch
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hm : MatchesExactly (crossoverGraphOver K) (deletionActive crossoverExternal x) m ↔
      MatchesExactly crossoverGraph (deletionActive crossoverExternal x) m := Iff.rfl
  by_cases h : MatchesExactly crossoverGraph (deletionActive crossoverExternal x) m
  · rw [ite_eq_left h, ite_eq_left (hm.mpr h), Int.cast_prod]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hm.mp hc)), Int.cast_zero]

/-- The checked table holds over every commutative ring, including characteristic two. -/
theorem crossover_deletionSignature_over {K : Type*} [CommRing K]
    (x : Fin 4 → Bool) :
    deletionSignature (crossoverGraphOver K) crossoverExternal x =
      (signedCrossoverValue x : K) := by
  rw [crossover_deletionSignature_cast, crossover_deletionSignature]

@[simp] theorem crossover_deletionSignature_0000 :
    deletionSignature crossoverGraph crossoverExternal ![false, false, false, false] = 1 := by
  rw [crossover_deletionSignature]
  rfl

@[simp] theorem crossover_deletionSignature_1010 :
    deletionSignature crossoverGraph crossoverExternal ![true, false, true, false] = 1 := by
  rw [crossover_deletionSignature]
  rfl

@[simp] theorem crossover_deletionSignature_0101 :
    deletionSignature crossoverGraph crossoverExternal ![false, true, false, true] = 1 := by
  rw [crossover_deletionSignature]
  rfl

@[simp] theorem crossover_deletionSignature_1111 :
    deletionSignature crossoverGraph crossoverExternal ![true, true, true, true] = -1 := by
  rw [crossover_deletionSignature]
  rfl

/-- Every other deletion pattern has zero matching sum. -/
theorem crossover_deletionSignature_zero (x : Fin 4 → Bool)
    (h : ¬ (x 0 = x 2 ∧ x 1 = x 3)) :
    deletionSignature crossoverGraph crossoverExternal x = 0 := by
  rw [crossover_deletionSignature]
  exact ite_eq_right h

end MatchgateWidth
