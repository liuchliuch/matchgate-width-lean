import MatchgateWidth.CircuitRealization

/-!
# Scalar-normalized finite matching-graph synthesis

At every positive width, replace one vacuum edge by an edge of weight `c`.
This produces the scalar `c`, including zero, before the ordinary local-gate
circuit is applied. The graph, its strip and disk drawings, its exact matching
signature, and the provenance of every edge weight are retained explicitly.
-/
namespace MatchgateWidth
noncomputable section

namespace WeightedGraph

/-- Change weights without changing any vertex, edge, or incidence. -/
def reweight {V E K : Type*} (G : WeightedGraph V E K) (w : E → K) :
    WeightedGraph V E K where
  left := G.left
  right := G.right
  loopless := G.loopless
  weight := w

end WeightedGraph

namespace PlaneArcDrawing

/-- A drawing is independent of the numerical edge weights. -/
def reweight {V E : Type*} {G : WeightedGraph V E ℂ}
    (D : PlaneArcDrawing G) (w : E → ℂ) : PlaneArcDrawing (G.reweight w) where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.edge
  edge_continuous := D.edge_continuous
  edge_injective := D.edge_injective
  edge_left := D.edge_left
  edge_right := D.edge_right
  interior_avoids_vertices := D.interior_avoids_vertices
  interiors_disjoint := D.interiors_disjoint

end PlaneArcDrawing

namespace StripDrawing

/-- Preserve the geometric strip bounds while changing edge weights. -/
def reweight {V E : Type*} {G : WeightedGraph V E ℂ} {n : ℕ}
    (D : StripDrawing G n) (w : E → ℂ) : StripDrawing (G.reweight w) n where
  toPlaneArcDrawing := D.toPlaneArcDrawing.reweight w
  vertex_x_lower := D.vertex_x_lower
  vertex_x_upper := D.vertex_x_upper
  vertex_y_lower := D.vertex_y_lower
  vertex_y_upper := D.vertex_y_upper
  edge_x_lower := D.edge_x_lower
  edge_x_upper := D.edge_x_upper
  edge_y_lower := D.edge_y_lower
  edge_y_upper := D.edge_y_upper

end StripDrawing

namespace StateDrawing

/-- Preserve the ordered output drawing while changing edge weights. -/
def reweight {V E : Type*} {G : WeightedGraph V E ℂ} {n : ℕ}
    {output : Fin n → V} (D : StateDrawing G output) (w : E → ℂ) :
    StateDrawing (G.reweight w) output where
  toStripDrawing := D.toStripDrawing.reweight w
  output_vertex := D.output_vertex

end StateDrawing

/-- A zero pin with its unique edge assigned an arbitrary scalar. -/
def scaledPinZeroGraph (c : ℂ) : WeightedGraph (Fin 2) (Fin 1) ℂ :=
  (pinZeroGraph ℂ).reweight (fun _ => c)

theorem scaledPinZero_deletionSignature (c : ℂ) (x : Fin 1 → Bool) :
    deletionSignature (scaledPinZeroGraph c) (fun _ => 0 : Fin 1 → Fin 2) x =
      c * deletionSignature (pinZeroGraph ℂ) (fun _ => 0 : Fin 1 → Fin 2) x := by
  classical
  rw [pinZero_deletionSignature]
  have hu : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hx : x = fun _ => x 0 := by ext i; fin_cases i; rfl
  rw [hx]
  unfold deletionSignature weightedPerfectMatch
  rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
  cases h : x 0 <;>
    simp +decide [MatchesExactly, matchingDegree, deletionActive, scaledPinZeroGraph,
      WeightedGraph.reweight, pinZeroGraph, Fin.forall_fin_succ]

namespace DrawnState
variable {n : ℕ}

/-- The same one-wire vacuum drawing, with its edge weight changed to `c`. -/
def scaledVacuumOne (c : ℂ) : DrawnState 1 where
  V := Fin 2
  E := Fin 1
  graph := scaledPinZeroGraph c
  output := fun _ => 0
  drawing := pinZeroStateDrawing.reweight (fun _ => c)

theorem signature_scaledVacuumOne (c : ℂ) (x : Fin 1 → Bool) :
    (scaledVacuumOne c).signature x = c * vacuumOne.signature x :=
  scaledPinZero_deletionSignature c x

/-- A positive-width vacuum row with exactly one edge of weight `c`.
No separate zero-width scalar component or realizability closure is used. -/
def scaledVacuum (c : ℂ) : (n : ℕ) → 0 < n → DrawnState n
  | 0, h => (Nat.not_lt_zero 0 h).elim
  | m + 1, _ => (vacuum m).parallel (scaledVacuumOne c)

theorem signature_scaledVacuum (c : ℂ) (hn : 0 < n) (x : Fin n → Bool) :
    (scaledVacuum c n hn).signature x = c * (vacuum n).signature x := by
  cases n with
  | zero => omega
  | succ n =>
    rw [scaledVacuum, vacuum, signature_parallel, signature_parallel,
      signature_scaledVacuumOne]
    ring

@[simp] theorem table_scaledVacuum (c : ℂ) (hn : 0 < n) :
    (scaledVacuum c n hn).table = fun S => c * pfaffianVacuum S := by
  funext S
  rw [table, signature_scaledVacuum]
  exact congrArg (c * ·) (congrFun (table_vacuum n) S)

/-- Assemble actual local-gate graphs from any drawn initial state. -/
def circuitFrom (W : DrawnState n) (gates : List (PfaffianLocalGate n ℂ)) : DrawnState n :=
  gates.foldr (fun g Z => Z.applyGate (DrawnWire.localGate g)) W

theorem table_circuitFrom (W : DrawnState n) (gates : List (PfaffianLocalGate n ℂ)) :
    (circuitFrom W gates).table = pfaffianCircuitAct gates W.table := by
  induction gates with
  | nil => rfl
  | cons g gates ih =>
    change ((circuitFrom W gates).applyGate (DrawnWire.localGate g)).table =
      g.act (pfaffianCircuitAct gates W.table)
    rw [table_applyLocal, ih]

theorem weightsIn_scaledVacuumOne (c : ℂ) (K : Subfield ℂ) (hc : c ∈ K) :
    (scaledVacuumOne c).weightsIn K := fun _ => hc

theorem weightsIn_scaledVacuum (c : ℂ) (hn : 0 < n) (K : Subfield ℂ) (hc : c ∈ K) :
    (scaledVacuum c n hn).weightsIn K := by
  cases n with
  | zero => omega
  | succ n =>
    exact weightsIn_parallel _ _ K (weightsIn_vacuum n K) (weightsIn_scaledVacuumOne c K hc)

theorem weightsIn_circuitFrom (W : DrawnState n)
    (gates : List (PfaffianLocalGate n ℂ)) (K : Subfield ℂ) (hW : W.weightsIn K)
    (hgates : ∀ g ∈ gates, g.coefficientsIn (· ∈ K)) :
    (circuitFrom W gates).weightsIn K := by
  induction gates with
  | nil => exact hW
  | cons g gates ih =>
    apply weightsIn_applyGate
    · exact ih (fun h hh => hgates h (by simp [hh]))
    · exact DrawnWire.weightsIn_localGate g K (hgates g (by simp))

end DrawnState

/-- Each actual circuit instruction is linear in the initial signature. -/
theorem PfaffianLocalGate.act_mul {n : ℕ} (g : PfaffianLocalGate n ℂ)
    (c : ℂ) (F : SubsetSignature n ℂ) :
    g.act (fun S => c * F S) = fun S => c * g.act F S := by
  cases g with
  | swap i j h =>
    funext S
    simp only [PfaffianLocalGate.act, pfaffianSignedSwap]
    ring
  | create i j h t =>
    funext S
    simp only [PfaffianLocalGate.act, pfaffianPairCreation]
    split_ifs <;> ring

/-- Scalar normalization is preserved through the entire gate list. -/
theorem pfaffianCircuitAct_mul {n : ℕ} (gates : List (PfaffianLocalGate n ℂ))
    (c : ℂ) (F : SubsetSignature n ℂ) :
    pfaffianCircuitAct gates (fun S => c * F S) =
      fun S => c * pfaffianCircuitAct gates F S := by
  induction gates with
  | nil => rfl
  | cons g gates ih =>
    rw [pfaffianCircuitAct_cons, pfaffianCircuitAct_cons, ih, PfaffianLocalGate.act_mul]

namespace DrawnState
variable {n : ℕ}

/-- Actual positive-width finite graph realizing the scaled principal Pfaffians. -/
def scaledPrincipalPfaffian (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    DrawnState n :=
  circuitFrom (scaledVacuum c n hn) (principalPfaffianCircuit A)

theorem table_scaledPrincipalPfaffian (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0) :
    (scaledPrincipalPfaffian c A hn).table =
      fun S => c * MatchgateWidth.principalPfaffian A S := by
  rw [scaledPrincipalPfaffian, table_circuitFrom, table_scaledVacuum,
    pfaffianCircuitAct_mul, principalPfaffianCircuit_correct A hA hdiag]

/-- Every edge weight remains in the field generated by the scalar and matrix entries. -/
theorem weightsIn_scaledPrincipalPfaffian (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (K : Subfield ℂ) (hc : c ∈ K)
    (hA : ∀ i j, i < j → A i j ∈ K) :
    (scaledPrincipalPfaffian c A hn).weightsIn K :=
  weightsIn_circuitFrom _ _ K (weightsIn_scaledVacuum c hn K hc)
    (principalPfaffianCircuit_subfield K A hA)

theorem signature_scaledPrincipalPfaffian (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0)
    (x : Fin n → Bool) :
    (scaledPrincipalPfaffian c A hn).signature x =
      c * MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x) := by
  have h := congrFun (table_scaledPrincipalPfaffian c A hn hA hdiag)
    (bridgeBitsEquiv (Fin n) x)
  have hx : circuitSubsetBits (bridgeBitsEquiv (Fin n) x) = x :=
    (bridgeBits_inverse _).symm.trans ((bridgeBitsEquiv (Fin n)).symm_apply_apply x)
  simpa only [table, hx] using h

end DrawnState

/-- Scalar principal-Pfaffian tables at positive width have genuine disk witnesses. -/
theorem scaledPrincipalPfaffian_diskRealizable {n : ℕ}
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0) :
    DiskRealizable (fun x => c * MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x)) := by
  let W := DrawnState.scaledPrincipalPfaffian c A hn
  have h := diskRealizable_of_finite_drawing W.graph W.output W.drawing.toDisk
  have he : deletionSignature W.graph W.output =
      (fun x => c * MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x)) := by
    funext x
    exact DrawnState.signature_scaledPrincipalPfaffian c A hn hA hdiag x
  rwa [he] at h

/-- Explicit finite ordered disk graph, with coefficient-field provenance,
for any scalar multiple of an alternating principal-Pfaffian table. -/
theorem scaledPrincipalPfaffian_diskWitness {n : ℕ}
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0)
    (K : Subfield ℂ) (hc : c ∈ K) (hK : ∀ i j, i < j → A i j ∈ K) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      ∀ x, deletionSignature G ext x =
        c * MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x) := by
  let W := DrawnState.scaledPrincipalPfaffian c A hn
  let v := (Fintype.equivFin W.V).symm
  let e := (Fintype.equivFin W.E).symm
  refine ⟨Fintype.card W.V, Fintype.card W.E, W.graph.reindex v e,
    (fun i => v.symm (W.output i)), ⟨W.drawing.toDisk.reindex v e⟩, ?_, ?_⟩
  · intro a
    exact DrawnState.weightsIn_scaledPrincipalPfaffian c A hn K hc hK (e a)
  · intro x
    rw [deletionSignature_reindex]
    exact DrawnState.signature_scaledPrincipalPfaffian c A hn hA hdiag x

/-- The same actual finite disk witness, exposed directly on selected subsets. -/
theorem scaledPrincipalPfaffian_subsetDiskWitness {n : ℕ}
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0)
    (K : Subfield ℂ) (hc : c ∈ K) (hK : ∀ i j, i < j → A i j ∈ K) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      ∀ S, deletionSignature G ext (circuitSubsetBits S) =
        c * MatchgateWidth.principalPfaffian A S := by
  obtain ⟨v, e, G, ext, hd, hw, hs⟩ :=
    scaledPrincipalPfaffian_diskWitness c A hn hA hdiag K hc hK
  refine ⟨v, e, G, ext, hd, hw, ?_⟩
  intro S
  rw [hs, ← bridgeBits_inverse, Equiv.apply_symm_apply]

end
end MatchgateWidth
