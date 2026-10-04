import MatchgateWidth.LocalDrawingPlacement

/-! # Actual affine insertion of a local matchgate drawing

Every finite disk-drawn matching graph can be placed in a prescribed round
vertex neighborhood by a positive scaling and arbitrary orientation-preserving
complex rotation. The graph, weights, incidence identities, external order,
and exact signature are unchanged.
-/
namespace MatchgateWidth
noncomputable section

namespace PlanarDrawing
variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- Insert a complete local matching graph in a prescribed disk centered at a
source-network vertex, with arbitrary positive-orientation similarity. -/
def insertAt (D : PlanarDrawing G ext) (center factor : ℂ) (hfactor : factor ≠ 0) :
    PlaneDrawing G := D.toPlaneDrawing.similarity center factor hfactor

@[simp] theorem insertAt_vertex (D : PlanarDrawing G ext) (center factor : ℂ)
    (hfactor : factor ≠ 0) (v : V) :
    (D.insertAt center factor hfactor).vertex v = center + factor * D.vertex v := rfl

@[simp] theorem insertAt_edge (D : PlanarDrawing G ext) (center factor : ℂ)
    (hfactor : factor ≠ 0) (e : E) (t : unitInterval) :
    (D.insertAt center factor hfactor).edge e t = center + factor * D.edge e t := rfl

/-- All inserted vertices lie in the chosen closed carrier disk. -/
theorem insertAt_vertex_mem (D : PlanarDrawing G ext) (center factor : ℂ)
    (hfactor : factor ≠ 0) (v : V) :
    (D.insertAt center factor hfactor).vertex v ∈ Metric.closedBall center ‖factor‖ := by
  rw [Metric.mem_closedBall, insertAt_vertex, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_mul]
  exact (mul_le_mul_of_nonneg_left (D.vertex_in_disk v) (norm_nonneg factor)).trans_eq (mul_one _)

/-- All inserted edges, not just their endpoints, lie in the same carrier. -/
theorem insertAt_edge_mem (D : PlanarDrawing G ext) (center factor : ℂ)
    (hfactor : factor ≠ 0) (e : E) (t : unitInterval) :
    (D.insertAt center factor hfactor).edge e t ∈ Metric.closedBall center ‖factor‖ := by
  rw [Metric.mem_closedBall, insertAt_edge, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_mul]
  exact (mul_le_mul_of_nonneg_left (D.edge_in_disk e t) (norm_nonneg factor)).trans_eq (mul_one _)

/-- The local external ports keep their exact original marked angle list in
the inserted disk's orientation-preserving frame. -/
theorem insertAt_external (D : PlanarDrawing G ext) (center factor : ℂ)
    (hfactor : factor ≠ 0) (i : Fin s) :
    (D.insertAt center factor hfactor).vertex (ext i) =
      center + factor * boundaryPoint (D.angle i) := by
  rw [insertAt_vertex,D.external_vertex]

end PlanarDrawing
end
end MatchgateWidth
