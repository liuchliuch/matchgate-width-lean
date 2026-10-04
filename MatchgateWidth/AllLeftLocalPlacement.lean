import MatchgateWidth.AllLeftGraphSubstitution
import MatchgateWidth.AllLeftGeometricLanes
import MatchgateWidth.PlaneDrawingFamilies
import MatchgateWidth.PlaneDrawingInsertion

/-! # Actual occurrence-wise local graph placement

Every local graph is chosen from its given disk witness and inserted by the
same complex similarity that is used for its annular connector bank. All
carrier bounds use the actual norm of that similarity, without a unit-frame
assumption. The primitive occurrence and scalar external indices are literal.
-/
namespace MatchgateWidth
noncomputable section
namespace LocalMatchingGraphFamily
variable {J : Type*} {arity : J → ℕ} (F : LocalMatchingGraphFamily J arity)

/-- Choose only the supplied actual local disk drawing. -/
def nativeDrawing (h : F.DiskDrawn) (j : J) : PlanarDrawing (F.graph j) (F.external j) :=
  Classical.choice (h j)

/-- Simultaneous occurrence-indexed insertion using the actual complex frame. -/
def inserted (h : F.DiskDrawn) (center factor : J → ℂ) (hnz : ∀ j, factor j ≠ 0)
    (j : J) : PlaneDrawing (F.graph j) :=
  (F.nativeDrawing h j).insertAt (center j) (factor j) (hnz j)

@[simp] theorem inserted_vertex (h : F.DiskDrawn) (center factor : J → ℂ)
    (hnz : ∀ j, factor j ≠ 0) (j : J) (v : Fin (F.vertices j)) :
    (F.inserted h center factor hnz j).vertex v =
      center j + factor j * (F.nativeDrawing h j).vertex v := rfl

@[simp] theorem inserted_external (h : F.DiskDrawn) (center factor : J → ℂ)
    (hnz : ∀ j, factor j ≠ 0) (j : J) (k : Fin (arity j)) :
    (F.inserted h center factor hnz j).vertex (F.external j k) =
      center j + factor j * boundaryPoint ((F.nativeDrawing h j).angle k) :=
  (F.nativeDrawing h j).insertAt_external _ _ _ _

/-- Closed local disks are genuine carriers for every vertex and edge. -/
def insertedCarriers (h : F.DiskDrawn) (center factor : J → ℂ)
    (hnz : ∀ j, factor j ≠ 0)
    (hdis : Pairwise (fun i j => Disjoint (Metric.closedBall (center i) ‖factor i‖)
      (Metric.closedBall (center j) ‖factor j‖))) :
    PlaneDrawing.FamilyCarriers (F.inserted h center factor hnz) where
  carrier j := Metric.closedBall (center j) ‖factor j‖
  disjoint := hdis
  vertex_mem j v := (F.nativeDrawing h j).insertAt_vertex_mem _ _ _ v
  edge_mem j e t := (F.nativeDrawing h j).insertAt_edge_mem _ _ _ e t

end LocalMatchingGraphFamily
namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
namespace OrderedPlanar

/-- The original drawing point of each actual primitive occurrence. -/
def primitiveCenter (Q : I.OrderedPlanar) (v : Fin a ⊕ Fin b) : ℂ :=
  Q.drawing.vertex (Sum.inl v)

theorem primitiveCenter_injective (Q : I.OrderedPlanar) : Function.Injective Q.primitiveCenter :=
  Q.drawing.vertex_injective.comp Sum.inl_injective

/-- Uniform actual placement radius for all primitive occurrences. This
includes empty occurrence families and nullary local matching graphs. -/
theorem exists_primitive_placement_radius (Q : I.OrderedPlanar)
    (hinside : ∀ v : Fin a ⊕ Fin b, ‖Q.primitiveCenter v‖ ≤ 1/2) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Pairwise (fun u v => Disjoint (Metric.closedBall (Q.primitiveCenter u) ρ)
        (Metric.closedBall (Q.primitiveCenter v) ρ)) ∧
      (∀ v z, z ∈ Metric.closedBall (Q.primitiveCenter v) ρ → ‖z‖ < 1) := by
  obtain ⟨ε,hε,hdis⟩ := finite_distinct_closedBall_disjoint _ Q.primitiveCenter_injective
  let ρ := min ε (1/4)
  have hρ : 0 < ρ := lt_min hε (by norm_num)
  refine ⟨ρ,hρ,?_,?_⟩
  · intro u v huv
    exact (hdis huv).mono (Metric.closedBall_subset_closedBall (min_le_left _ _))
      (Metric.closedBall_subset_closedBall (min_le_left _ _))
  · intro v z hz
    have hz' : ‖z-Q.primitiveCenter v‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hb := norm_add_le (z-Q.primitiveCenter v) (Q.primitiveCenter v)
    rw [sub_add_cancel] at hb
    have hr : ρ ≤ 1/4 := min_le_right _ _
    linarith [hinside v]

/-- Arbitrary small similarity factors inherit all cross-occurrence carrier
separation, including left/right pairs. -/
theorem primitive_variable_carriers_disjoint (Q : I.OrderedPlanar) {ρ : ℝ}
    (hdis : Pairwise (fun u v => Disjoint (Metric.closedBall (Q.primitiveCenter u) ρ)
      (Metric.closedBall (Q.primitiveCenter v) ρ)))
    (factor : Fin a ⊕ Fin b → ℂ) (hfactor : ∀ v, ‖factor v‖ ≤ ρ) :
    Pairwise (fun u v => Disjoint (Metric.closedBall (Q.primitiveCenter u) ‖factor u‖)
      (Metric.closedBall (Q.primitiveCenter v) ‖factor v‖)) := by
  intro u v huv
  exact (hdis huv).mono (Metric.closedBall_subset_closedBall (hfactor u))
    (Metric.closedBall_subset_closedBall (hfactor v))

/-- Left occurrence placement with literally the graph family's chosen frame. -/
def placedLeft (Q : I.OrderedPlanar) (L : I.LeftMatchingFamily (t := t))
    (hL : L.DiskDrawn) (factor : Fin a → ℂ) (hnz : ∀ v, factor v ≠ 0) :=
  L.inserted hL (fun v => Q.primitiveCenter (Sum.inl v)) factor hnz

/-- Right occurrence placement with literally the graph family's chosen frame. -/
def placedRight (Q : I.OrderedPlanar) (R : I.RightMatchingFamily (t := t))
    (hR : R.DiskDrawn) (factor : Fin b → ℂ) (hnz : ∀ v, factor v ≠ 0) :=
  R.inserted hR (fun v => Q.primitiveCenter (Sum.inr v)) factor hnz

/-- Endpoint equation for an internal bridge in the inserted left family. -/
theorem placedLeft_internal_endpoint (Q : I.OrderedPlanar) (L : I.LeftMatchingFamily (t := t))
    (hL : L.DiskDrawn) (factor : Fin a → ℂ) (hnz : ∀ v, factor v ≠ 0)
    (e : Fin c) (k : Fin t) :
    let q := I.internalLeftWire (finProdFinEquiv (e,k))
    (Q.placedLeft L hL factor hnz q.1).vertex (L.external q.1 q.2) =
      let v := (I.leftIncidence.symm (Sum.inl e)).1
      let i := (I.leftIncidence.symm (Sum.inl e)).2
      Q.primitiveCenter (Sum.inl v) + factor v *
        boundaryPoint ((L.nativeDrawing hL v).angle (finProdFinEquiv (i,k.rev))) := by
  dsimp only
  rw [I.internalLeftWire_eq_geometricLane]
  exact L.inserted_external _ _ _ _ _ _

/-- Endpoint equation for the unchanged semantic position at the right end. -/
theorem placedRight_internal_endpoint (Q : I.OrderedPlanar) (R : I.RightMatchingFamily (t := t))
    (hR : R.DiskDrawn) (factor : Fin b → ℂ) (hnz : ∀ v, factor v ≠ 0)
    (e : Fin c) (k : Fin t) :
    let q := I.internalRightWire (finProdFinEquiv (e,k))
    (Q.placedRight R hR factor hnz q.1).vertex (R.external q.1 q.2) =
      let v := (I.rightIncidence.symm e).1
      let i := (I.rightIncidence.symm e).2
      Q.primitiveCenter (Sum.inr v) + factor v *
        boundaryPoint ((R.nativeDrawing hR v).angle (finProdFinEquiv (i,k))) := by
  dsimp only
  rw [I.internalRightWire_eq_local_position]
  exact R.inserted_external _ _ _ _ _ _

/-- Endpoint equation at the exposed left port preserves its displayed index. -/
theorem placedLeft_boundary_endpoint (Q : I.OrderedPlanar) (L : I.LeftMatchingFamily (t := t))
    (hL : L.DiskDrawn) (factor : Fin a → ℂ) (hnz : ∀ v, factor v ≠ 0)
    (p : Fin n) (k : Fin t) :
    let q := I.boundaryLeftWire (finProdFinEquiv (p,k))
    (Q.placedLeft L hL factor hnz q.1).vertex (L.external q.1 q.2) =
      let v := (I.leftIncidence.symm (Sum.inr p)).1
      let i := (I.leftIncidence.symm (Sum.inr p)).2
      Q.primitiveCenter (Sum.inl v) + factor v *
        boundaryPoint ((L.nativeDrawing hL v).angle (finProdFinEquiv (i,k))) := by
  dsimp only
  rw [I.boundaryLeftWire_eq_geometricLane]
  exact L.inserted_external _ _ _ _ _ _

end OrderedPlanar
end AllLeftGadget
end
end MatchgateWidth
