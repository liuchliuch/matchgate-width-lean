import MatchgateWidth.DiskExteriorAccess

/-! # Actual placement of local matchgate drawings in prescribed carriers
The graph, weights, external labels and deletion signature do not change.
Only its embedding is moved by an orientation-preserving complex similarity.
-/
namespace MatchgateWidth
noncomputable section

namespace PlaneDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ}

/-- Any continuous injective ambient map transports every drawing obligation. -/
def mapInjective (P : PlaneDrawing G) (f : ℂ → ℂ)
    (hf : Continuous f) (hi : Function.Injective f) : PlaneDrawing G where
  vertex := fun v => f (P.vertex v)
  vertex_injective := hi.comp P.vertex_injective
  edge := fun e t => f (P.edge e t)
  edge_continuous := fun e => hf.comp (P.edge_continuous e)
  edge_injective := fun e => hi.comp (P.edge_injective e)
  edge_left := fun e => congrArg f (P.edge_left e)
  edge_right := fun e => congrArg f (P.edge_right e)
  interior_avoids_vertices := fun e t ht0 ht1 v h => P.interior_avoids_vertices e t ht0 ht1 v (hi h)
  interiors_disjoint := fun e g heg t u ht0 ht1 hu0 hu1 h =>
    P.interiors_disjoint e g heg t u ht0 ht1 hu0 hu1 (hi h)

def similarity (P : PlaneDrawing G) (c a : ℂ) (ha : a ≠ 0) : PlaneDrawing G :=
  P.mapInjective (fun z => c+a*z) (by fun_prop)
    (fun _ _ h => mul_left_cancel₀ ha (add_left_cancel h))

@[simp] theorem similarity_vertex (P : PlaneDrawing G) (c a : ℂ) (ha : a ≠ 0) (v : V) :
    (P.similarity c a ha).vertex v = c+a*P.vertex v := rfl

@[simp] theorem similarity_edge (P : PlaneDrawing G) (c a : ℂ) (ha : a ≠ 0)
    (e : E) (t : unitInterval) :
    (P.similarity c a ha).edge e t = c+a*P.edge e t := rfl

end PlaneDrawing

namespace PlanarDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ} {s : ℕ} {ext : Fin s → V}

/-- Place a unit-disk witness into an arbitrary complex disk carrier. -/
def place (D : PlanarDrawing G ext) (c a : ℂ) (ha : a ≠ 0) : PlaneDrawing G :=
  D.toPlaneDrawing.similarity c a ha

theorem place_vertex_in_ball (D : PlanarDrawing G ext) (c a : ℂ) (ha : a ≠ 0) (v : V) :
    ‖(D.place c a ha).vertex v-c‖ ≤ ‖a‖ := by
  change ‖c+a*D.vertex v-c‖ ≤ _
  rw [add_sub_cancel_left,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg a) (D.vertex_in_disk v)

theorem place_edge_in_ball (D : PlanarDrawing G ext) (c a : ℂ) (ha : a ≠ 0)
    (e : E) (t : unitInterval) : ‖(D.place c a ha).edge e t-c‖ ≤ ‖a‖ := by
  change ‖c+a*D.edge e t-c‖ ≤ _
  rw [add_sub_cancel_left,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg a) (D.edge_in_disk e t)

theorem place_external_vertex (D : PlanarDrawing G ext) (c a : ℂ) (ha : a ≠ 0) (i : Fin s) :
    (D.place c a ha).vertex (ext i) = c+a*boundaryPoint (D.angle i) := by
  change c+a*D.vertex (ext i)=_
  rw [D.external_vertex]

theorem place_external_norm (D : PlanarDrawing G ext) (c a : ℂ) (ha : a ≠ 0) (i : Fin s) :
    ‖(D.place c a ha).vertex (ext i)-c‖ = ‖a‖ := by
  rw [place_external_vertex,add_sub_cancel_left,norm_mul,norm_boundaryPoint,mul_one]

end PlanarDrawing
end
end MatchgateWidth
