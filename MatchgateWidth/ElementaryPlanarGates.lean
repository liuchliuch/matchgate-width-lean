import MatchgateWidth.SquareDiskDrawing
import MatchgateWidth.CrossoverGadget

/-!
# Explicit elementary disk-drawn matching gates

All signature assertions use the actual finite weighted matching sum. No
arbitrary-signature realization or topological normalization is asserted.
-/

namespace MatchgateWidth

noncomputable section

/-- Two nested unit wires and a variable edge joining the first two ports. -/
def pairCreationGraph {K : Type*} [CommSemiring K] (t : K) :
    WeightedGraph (Fin 4) (Fin 3) K where
  left := ![0, 1, 0]
  right := ![3, 2, 1]
  loopless := by decide
  weight := ![1, 1, t]

/-- Full deletion-coordinate table, including all zero entries. -/
def pairCreationValue {K : Type*} [CommSemiring K] (t : K) (x : Fin 4 → Bool) : K :=
  if x 0 = x 3 ∧ x 1 = x 2 then 1
  else if x 0 = false ∧ x 1 = false ∧ x 2 = true ∧ x 3 = true then t else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- The table holds over every commutative semiring, hence over arbitrary fields. -/
theorem pairCreation_deletionSignature {K : Type*} [CommSemiring K]
    (t : K) (x : Fin 4 → Bool) :
    deletionSignature (pairCreationGraph t) id x = pairCreationValue t x := by
  classical
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    ext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp +decide [deletionSignature, weightedPerfectMatch, hu, MatchesExactly,
      matchingDegree, deletionActive, pairCreationGraph, pairCreationValue,
      Fin.forall_fin_succ]

/-- The right-hand ports are reversed when read as two wire coordinates. The
first argument records the initial state, the second the final state. -/
def pairCreationMatrix {K : Type*} [CommSemiring K] (t : K)
    (a b : Fin 2 → Bool) : K :=
  deletionSignature (pairCreationGraph t) id ![a 0, a 1, b 1, b 0]

/-- With false = vacuum and true = occupied, the gate is identity plus the
vacuum-to-double-occupancy matrix entry of coefficient `t`. -/
theorem pairCreationMatrix_eq {K : Type*} [CommSemiring K]
    (t : K) (a b : Fin 2 → Bool) :
    pairCreationMatrix t a b = (if a = b then 1 else 0) +
      (if a = (fun _ => false) ∧ b = (fun _ => true) then t else 0) := by
  rw [pairCreationMatrix, pairCreation_deletionSignature]
  have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by ext i; fin_cases i <;> rfl
  rw [ha, hb]
  generalize a 0 = a₀
  generalize a 1 = a₁
  generalize b 0 = b₀
  generalize b 1 = b₁
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    simp [pairCreationValue, funext_iff, Fin.forall_fin_succ]

/-- A genuine disk drawing of the pair-creation graph. Its external corners
have strictly increasing angles 1/8, 3/8, 5/8, 7/8. -/
def pairCreationDrawing (z : ℂ) : PlanarDrawing (pairCreationGraph z) id where
  vertex := squareCorners
  vertex_injective := squareCorners_injective
  vertex_in_disk := squareCorners_in_disk
  edge := fun e => straightArc (squareCorners ((pairCreationGraph z).left e))
    (squareCorners ((pairCreationGraph z).right e))
  edge_continuous := fun e => continuous_straightArc _ _
  edge_injective := fun e => straightArc_injective
    (fun h => (pairCreationGraph z).loopless e (squareCorners_injective h))
  edge_left := fun e => straightArc_zero _ _
  edge_right := fun e => straightArc_one _ _
  edge_in_disk := fun e => straightArc_in_disk
    (squareCorners_in_disk _) (squareCorners_in_disk _)
  interior_avoids_vertices := by
    intro e t ht₀ ht₁ v h
    have ht0 : 0 < (t : ℝ) := ht₀
    have ht1 : (t : ℝ) < 1 := ht₁
    fin_cases e <;> fin_cases v <;>
      norm_num [pairCreationGraph, squareCorners] at h <;>
      linarith
  interiors_disjoint := by
    intro e f hef t u ht₀ ht₁ hu₀ hu₁ h
    have ht0 : 0 < (t : ℝ) := ht₀
    have ht1 : (t : ℝ) < 1 := ht₁
    have hu0 : 0 < (u : ℝ) := hu₀
    have hu1 : (u : ℝ) < 1 := hu₁
    fin_cases e <;> fin_cases f <;>
      norm_num at hef <;> norm_num [pairCreationGraph, squareCorners] at h <;>
      linarith
  external_injective := Function.injective_id
  angle := squareAngles
  angle_pos := squareAngles_pos
  angle_lt_one := squareAngles_lt_one
  angle_strictMono := squareAngles_strictMono
  external_vertex := squareCorners_boundary

/-- Pair creation is exactly disk realizable, with no extra normalization. -/
theorem pairCreation_diskRealizable (z : ℂ) : DiskRealizable (pairCreationValue z) := by
  refine ⟨4, 3, pairCreationGraph z, id, ⟨pairCreationDrawing z⟩, ?_⟩
  intro x
  exact (pairCreation_deletionSignature z x).symm

/-- Vertices of the signed crossover: four square corners and the two
midpoints of the vertical sides. The external order is counterclockwise. -/
def crossoverDiskVertices : Fin 6 → ℂ :=
  ![squarePoint 1 1, squarePoint (-1) 1, squarePoint (-1) (-1),
    squarePoint 1 (-1), squarePoint 1 0, squarePoint (-1) 0]

theorem crossoverDiskVertices_injective : Function.Injective crossoverDiskVertices := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [crossoverDiskVertices] at *

theorem crossoverDiskVertices_in_disk (i : Fin 6) : ‖crossoverDiskVertices i‖ ≤ 1 := by
  fin_cases i <;> apply squarePoint_in_disk <;> norm_num

set_option maxHeartbeats 800000 in
/-- A fully verified straight-arc disk drawing of the seven-edge signed
crossover. In particular, the negative middle edge crosses no other edge. -/
def crossoverDiskDrawing : PlanarDrawing (crossoverGraphOver ℂ) crossoverExternal where
  vertex := crossoverDiskVertices
  vertex_injective := crossoverDiskVertices_injective
  vertex_in_disk := crossoverDiskVertices_in_disk
  edge := fun e => straightArc (crossoverDiskVertices (crossoverLeft e))
    (crossoverDiskVertices (crossoverRight e))
  edge_continuous := fun e => continuous_straightArc _ _
  edge_injective := fun e => straightArc_injective
    (fun h => crossoverGraph.loopless e (crossoverDiskVertices_injective h))
  edge_left := fun e => straightArc_zero _ _
  edge_right := fun e => straightArc_one _ _
  edge_in_disk := fun e => straightArc_in_disk
    (crossoverDiskVertices_in_disk _) (crossoverDiskVertices_in_disk _)
  interior_avoids_vertices := by
    intro e t ht₀ ht₁ v h
    have ht0 : 0 < (t : ℝ) := ht₀
    have ht1 : (t : ℝ) < 1 := ht₁
    fin_cases e <;> fin_cases v <;>
      norm_num [crossoverLeft, crossoverRight, crossoverDiskVertices] at h <;>
      (try simp only [← Set.Icc.coe_eq_zero, ← Set.Icc.coe_eq_one] at h) <;> linarith
  interiors_disjoint := by
    intro e f hef t u ht₀ ht₁ hu₀ hu₁ h
    have ht0 : 0 < (t : ℝ) := ht₀
    have ht1 : (t : ℝ) < 1 := ht₁
    have hu0 : 0 < (u : ℝ) := hu₀
    have hu1 : (u : ℝ) < 1 := hu₁
    fin_cases e <;> fin_cases f <;>
      norm_num at hef <;> norm_num [crossoverLeft, crossoverRight, crossoverDiskVertices] at h <;>
      (try simp only [← Set.Icc.coe_eq_zero, ← Set.Icc.coe_eq_one] at h) <;> linarith
  external_injective := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [crossoverExternal]
  angle := squareAngles
  angle_pos := squareAngles_pos
  angle_lt_one := squareAngles_lt_one
  angle_strictMono := squareAngles_strictMono
  external_vertex := by
    intro i
    have h := squareCorners_boundary i
    fin_cases i <;> exact h

/-- The actual signed crossover signature has an explicit ordered disk drawing. -/
theorem signedCrossover_diskRealizable :
    DiskRealizable (fun x => (signedCrossoverValue x : ℂ)) := by
  refine ⟨6, 7, crossoverGraphOver ℂ, crossoverExternal, ⟨crossoverDiskDrawing⟩, ?_⟩
  intro x
  exact (crossover_deletionSignature_over x).symm

/-- Unit edge with its first endpoint external: the zero pin. -/
def pinZeroGraph (K : Type*) [CommSemiring K] : WeightedGraph (Fin 2) (Fin 1) K where
  left := fun _ => 0
  right := fun _ => 1
  loopless := by intro e; decide
  weight := fun _ => 1

/-- One isolated external vertex: the one pin. -/
def pinOneGraph (K : Type*) [CommSemiring K] : WeightedGraph (Fin 1) (Fin 0) K where
  left := Fin.elim0
  right := Fin.elim0
  loopless := fun e => e.elim0
  weight := Fin.elim0

theorem pinZero_deletionSignature {K : Type*} [CommSemiring K] (x : Fin 1 → Bool) :
    deletionSignature (pinZeroGraph K) (fun _ => 0 : Fin 1 → Fin 2) x =
      if x 0 = false then 1 else 0 := by
  classical
  have hu : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hx : x = fun _ => x 0 := by ext i; fin_cases i; rfl
  rw [hx]
  unfold deletionSignature weightedPerfectMatch
  rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
  cases h : x 0 <;>
    simp +decide [MatchesExactly, matchingDegree, deletionActive, pinZeroGraph,
      Fin.forall_fin_succ]

theorem pinOne_deletionSignature {K : Type*} [CommSemiring K] (x : Fin 1 → Bool) :
    deletionSignature (pinOneGraph K) id x = if x 0 = true then 1 else 0 := by
  classical
  have hu : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  have hx : x = fun _ => x 0 := by ext i; fin_cases i; rfl
  rw [hx]
  unfold deletionSignature weightedPerfectMatch
  rw [hu, Finset.sum_singleton]
  cases h : x 0 <;>
    simp +decide [MatchesExactly, matchingDegree, deletionActive, pinOneGraph]

def pinZeroVertices : Fin 2 → ℂ := ![squarePoint 1 1, squarePoint 0 0]

theorem pinZeroVertices_injective : Function.Injective pinZeroVertices := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [pinZeroVertices] at *

theorem pinZeroVertices_in_disk (i : Fin 2) : ‖pinZeroVertices i‖ ≤ 1 := by
  fin_cases i <;> apply squarePoint_in_disk <;> norm_num

/-- A radial unit-edge drawing of the zero pin. -/
def pinZeroDrawing : PlanarDrawing (pinZeroGraph ℂ) (fun _ => 0 : Fin 1 → Fin 2) where
  vertex := pinZeroVertices
  vertex_injective := pinZeroVertices_injective
  vertex_in_disk := pinZeroVertices_in_disk
  edge := fun _ => straightArc (pinZeroVertices 0) (pinZeroVertices 1)
  edge_continuous := fun _ => continuous_straightArc _ _
  edge_injective := fun _ => straightArc_injective (by
    intro h
    have hh := pinZeroVertices_injective h
    norm_num at hh)
  edge_left := fun _ => straightArc_zero _ _
  edge_right := fun _ => straightArc_one _ _
  edge_in_disk := fun _ => straightArc_in_disk
    (pinZeroVertices_in_disk _) (pinZeroVertices_in_disk _)
  interior_avoids_vertices := by
    intro e t ht₀ ht₁ v h
    have ht0 : 0 < (t : ℝ) := ht₀
    have ht1 : (t : ℝ) < 1 := ht₁
    fin_cases v <;> norm_num [pinZeroVertices] at h <;> (try simp only [← Set.Icc.coe_eq_zero] at h) <;> linarith
  interiors_disjoint := by
    intro e f hef
    exact (hef (Subsingleton.elim _ _)).elim
  external_injective := Function.injective_of_subsingleton _
  angle := fun _ => 1/8
  angle_pos := by intro i; norm_num
  angle_lt_one := by intro i; norm_num
  angle_strictMono := by intro i j hij; have h : i = j := Subsingleton.elim _ _; subst j; exact (lt_irrefl _ hij).elim
  external_vertex := fun _ => squarePoint_one_one

/-- The one pin consists of just one boundary vertex and no arcs. -/
def pinOneDrawing : PlanarDrawing (pinOneGraph ℂ) id where
  vertex := fun _ => squarePoint 1 1
  vertex_injective := Function.injective_of_subsingleton _
  vertex_in_disk := fun _ => squarePoint_in_disk (by norm_num)
  edge := Fin.elim0
  edge_continuous := fun e => e.elim0
  edge_injective := fun e => e.elim0
  edge_left := fun e => e.elim0
  edge_right := fun e => e.elim0
  edge_in_disk := fun e => e.elim0
  interior_avoids_vertices := fun e => e.elim0
  interiors_disjoint := fun e => e.elim0
  external_injective := Function.injective_id
  angle := fun _ => 1/8
  angle_pos := by intro i; norm_num
  angle_lt_one := by intro i; norm_num
  angle_strictMono := by intro i j hij; have h : i = j := Subsingleton.elim _ _; subst j; exact (lt_irrefl _ hij).elim
  external_vertex := fun _ => squarePoint_one_one

theorem pinZero_diskRealizable :
    DiskRealizable (fun x : Fin 1 → Bool => if x 0 = false then (1 : ℂ) else 0) := by
  refine ⟨2, 1, pinZeroGraph ℂ, (fun _ => 0), ⟨pinZeroDrawing⟩, ?_⟩
  intro x
  exact (pinZero_deletionSignature x).symm

theorem pinOne_diskRealizable :
    DiskRealizable (fun x : Fin 1 → Bool => if x 0 = true then (1 : ℂ) else 0) := by
  refine ⟨1, 0, pinOneGraph ℂ, id, ⟨pinOneDrawing⟩, ?_⟩
  intro x
  exact (pinOne_deletionSignature x).symm

/-- Input/output-reversed transfer kernel of the signed crossover. -/
def crossoverMatrix {K : Type*} [CommRing K] (a b : Fin 2 → Bool) : K :=
  deletionSignature (crossoverGraphOver K) crossoverExternal ![a 0, a 1, b 1, b 0]

/-- The crossover swaps the two wires and adds the fermionic sign precisely
on the doubly occupied state. -/
theorem crossoverMatrix_eq {K : Type*} [CommRing K] (a b : Fin 2 → Bool) :
    crossoverMatrix (K := K) a b =
      if b = (fun i => a i.rev) then
        if a 0 = true ∧ a 1 = true then -1 else 1
      else 0 := by
  rw [crossoverMatrix, crossover_deletionSignature_over]
  have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by ext i; fin_cases i <;> rfl
  rw [ha, hb]
  generalize a 0 = a₀
  generalize a 1 = a₁
  generalize b 0 = b₀
  generalize b 1 = b₁
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    simp [signedCrossoverValue, funext_iff, Fin.forall_fin_succ, Fin.rev]

/-- Pair creation uses no field element beyond its parameter and the units. -/
theorem pairCreation_weights_mem (F : Subfield ℂ) {z : ℂ} (hz : z ∈ F) (e : Fin 3) :
    (pairCreationGraph z).weight e ∈ F := by
  fin_cases e <;> simp [pairCreationGraph, hz]

/-- The signed crossover is defined over every coefficient subfield. -/
theorem crossover_weights_mem (F : Subfield ℂ) (e : Fin 7) :
    (crossoverGraphOver ℂ).weight e ∈ F := by
  fin_cases e <;> simp [crossoverGraphOver, crossoverGraph]

theorem pinZero_weights_mem (F : Subfield ℂ) (e : Fin 1) :
    (pinZeroGraph ℂ).weight e ∈ F := by simp [pinZeroGraph]

theorem pinOne_weights_mem (F : Subfield ℂ) (e : Fin 0) :
    (pinOneGraph ℂ).weight e ∈ F := e.elim0

end
end MatchgateWidth
