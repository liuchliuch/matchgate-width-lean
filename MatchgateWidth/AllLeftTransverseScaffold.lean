import MatchgateWidth.OrderedPolygonalReplacement
import MatchgateWidth.IndexedDrawingCollars
import MatchgateWidth.SimplePolygonalRibbons
import MatchgateWidth.AllLeftCutAngles
import MatchgateWidth.AllLeftRibbonFamily

/-! # Derived source polygonal collars and simultaneous transverse corridors

This construction starts from the actual ordered-planar gadget and makes all
finite geometric choices through genuine existence theorems. Every corridor
is cut from its original source edge, and every transverse route stays in a
pairwise-disjoint open neighborhood outside the smaller vertex collars.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget
variable {S : LabelledShape} {a b c n : ℕ} (I : AllLeftGadget S a b c n)

/-- Concrete geometric data produced by normalization, exact-trace indexing,
round collar selection, radial trimming and positive transverse sections. -/
structure TransverseScaffold where
  ordered : I.OrderedPlanar
  polygonal : ∀ e, IsPolygonalPath (ordered.drawing.edgePath e)
  interior : ∀ e u, 0 < u → u < 1 → ‖ordered.drawing.edge e u‖ < 1
  primitive_bound : ∀ v : Fin a ⊕ Fin b, ‖ordered.primitiveCenter v‖ ≤ 1/2
  boundary_germ : ∀ p : Fin n, ∃ κ : ℝ, 0 < κ ∧ ∃ ρ : unitInterval, 0 < ρ ∧
    ∀ u : unitInterval, u ≤ ρ →
      ordered.drawing.edge (Sum.inr p) (LabelledInstance.reverseParameter u) =
        boundaryPoint (ordered.drawing.angle p) +
          (u:ℝ) • (κ • (-boundaryPoint (ordered.drawing.angle p)))
  indexed : ordered.drawing.IndexedRoutes
  collars : indexed.Collars
  route : ∀ e, TransversePolygonalRoute (indexed e).edgeCount
  route_vertex : ∀ e, (route e).vertex =
    (collars.trimRoute (2*collars.radius) (by linarith [collars.positive])
      (by linarith [collars.positive]) e).vertex
  openCarrier : (Fin c ⊕ Fin n) → Set ℂ
  carrier_open : ∀ e, IsOpen (openCarrier e)
  carrier_disjoint : Pairwise (fun e f => Disjoint (openCarrier e) (openCarrier f))
  route_carrier_subset : ∀ e i, (route e).carrier i ⊆ openCarrier e
  carrier_geometry : ∀ e z, z ∈ openCarrier e → ‖z‖ < 1 ∧
    ∀ v : (Fin a ⊕ Fin b) ⊕ Fin n, collars.radius < dist z (ordered.drawing.vertex v)

/-- An actual ordered source gadget supplies all scaffold data. No substituted
routing or output signature condition is a premise of this construction. -/
theorem OrderedPlanar.exists_transverseScaffold (P : I.OrderedPlanar) :
    ∃ K : I.TransverseScaffold, K.ordered.drawing.angle = P.drawing.angle := by
  classical
  obtain ⟨Q,hpoly,hint,hprim,hangle,_,_,hboundary⟩ :=
    P.exists_polygonal_ordered_drawing_with_boundary_germs
  obtain ⟨R⟩ := Q.drawing.exists_indexed_routes hpoly
  obtain ⟨C⟩ := R.exists_collars
  have hδ : 0 < 2*C.radius := mul_pos (by norm_num) C.positive
  have hδmax : 2*C.radius ≤ 4*C.radius := by linarith [C.positive]
  obtain ⟨U,hU,hsub,hdis,hbound⟩ := C.open_carriers hint (2*C.radius) hδ hδmax
    C.radius (by linarith [C.positive])
  let T := C.trimRoute (2*C.radius) hδ hδmax
  have hex (e : Fin c ⊕ Fin n) :
      ∃ B : TransversePolygonalRoute (R e).edgeCount,
        B.vertex = (T e).vertex ∧ ∀ i, B.carrier i ⊆ U e := by
    apply simplePolygon_exists_transverseRoute (T e).vertex (T e).nonzero
      (T e).adjacent (T e).nonadjacent (fun _ => U e) (fun _ => hU e)
    intro i z hz
    apply hsub e
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [range_straightArc] at hz
    exact hz
  choose B hB hBU using hex
  refine ⟨{
    ordered := Q
    polygonal := hpoly
    interior := hint
    primitive_bound := hprim
    boundary_germ := hboundary
    indexed := R
    collars := C
    route := B
    route_vertex := hB
    openCarrier := U
    carrier_open := hU
    carrier_disjoint := hdis
    route_carrier_subset := hBU
    carrier_geometry := hbound },hangle⟩

namespace TransverseScaffold
variable {I} (K : I.TransverseScaffold)

def cutRadius : ℝ := 2*K.collars.radius

theorem cutRadius_pos : 0 < K.cutRadius := mul_pos (by norm_num) K.collars.positive

theorem route_source (e : Fin c ⊕ Fin n) :
    (K.route e).vertex 0 = (K.indexed e).radialSourceCut K.cutRadius := by
  rw [K.route_vertex]
  exact (K.collars.trimRoute _ _ _ e).source

theorem route_target (e : Fin c ⊕ Fin n) :
    (K.route e).vertex (Fin.last (K.indexed e).edgeCount) =
      (K.indexed e).radialTargetCut K.cutRadius := by
  rw [K.route_vertex]
  exact (K.collars.trimRoute _ _ _ e).target

theorem route_carriers_disjoint : Pairwise (fun e f =>
    Disjoint (⋃ i, (K.route e).carrier i) (⋃ j, (K.route f).carrier j)) := by
  intro e f hef
  exact (K.carrier_disjoint hef).mono
    (Set.iUnion_subset fun i => K.route_carrier_subset e i)
    (Set.iUnion_subset fun i => K.route_carrier_subset f i)

/-- All physical scalar middle paths share one common positive width, with
all within-edge and across-edge disjointness already derived. -/
theorem exists_uniform_middle_paths (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      (∀ e, (K.route e).Width ε) ∧
      ∃ q : (e : Fin c ⊕ Fin n) → (k : Fin t) →
        Path ((K.route e).laneVertex (physicalLaneOffset ε e k) 0)
          ((K.route e).laneVertex (physicalLaneOffset ε e k) (Fin.last (K.indexed e).edgeCount)),
      (∀ e k, Function.Injective (q e k) ∧ IsPolygonalPath (q e k) ∧
        Set.range (q e k) = (K.route e).laneSupport (physicalLaneOffset ε e k)) ∧
      Pairwise (fun x y : (Fin c ⊕ Fin n) × Fin t =>
        Disjoint (Set.range (q x.1 x.2)) (Set.range (q y.1 y.2))) :=
  exists_uniform_physical_ribbon_family _ K.route (fun e => (K.indexed e).positive)
    K.route_carriers_disjoint

theorem left_cut_angles (v : Fin a) :
    Nonempty (OrderedRayAngles (K.ordered.leftCutVector K.indexed K.cutRadius v)) :=
  K.ordered.leftCutVector_ordered K.indexed K.cutRadius K.cutRadius_pos v

theorem right_cut_angles (v : Fin b) :
    Nonempty (OrderedRayAngles (K.ordered.rightCutVector K.indexed K.cutRadius v)) :=
  K.ordered.rightCutVector_ordered K.indexed K.cutRadius K.cutRadius_pos v

theorem boundary_target (p : Fin n) :
    (K.route (Sum.inr p)).vertex (Fin.last (K.indexed (Sum.inr p)).edgeCount) =
      ((1-K.cutRadius:ℝ):ℂ)*boundaryPoint (K.ordered.drawing.angle p) := by
  rw [K.route_target]
  exact K.ordered.boundary_radialTargetCut K.indexed p (K.boundary_germ p) K.cutRadius K.cutRadius_pos

end TransverseScaffold
end AllLeftGadget
end
end MatchgateWidth
