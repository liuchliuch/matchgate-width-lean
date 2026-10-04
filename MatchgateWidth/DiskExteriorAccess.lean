import MatchgateWidth.PlaneExteriorAccess

/-!
# Radial exterior access from a disk drawing

This is an unchanged-graph construction: the original vertices and edge arcs
are retained, and each external point is joined radially to the circle of
radius two. It does not assert the converse geometric normalization theorem
for arbitrary ordered outer-face embeddings.
-/
namespace MatchgateWidth
noncomputable section

namespace PlanarDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ} {s : ℕ} {ext : Fin s → V}

/-- Forget only the disk and external-boundary constraints. -/
def toPlaneDrawing (D : PlanarDrawing G ext) : PlaneDrawing G where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.edge
  edge_continuous := D.edge_continuous
  edge_injective := D.edge_injective
  edge_left := D.edge_left
  edge_right := D.edge_right
  interior_avoids_vertices := D.interior_avoids_vertices
  interiors_disjoint := D.interiors_disjoint

/-- The radial segment from an external vertex to twice that vertex. -/
def radialAccess (D : PlanarDrawing G ext) (i : Fin s) :
    Path (D.vertex (ext i)) ((2 : ℂ) * boundaryPoint (D.angle i)) where
  toFun := fun t => ((1 + (t : ℝ) : ℝ) : ℂ) * D.vertex (ext i)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [D.external_vertex]; norm_num

@[simp] theorem radialAccess_apply (D : PlanarDrawing G ext) (i : Fin s)
    (t : unitInterval) :
    D.radialAccess i t = ((1 + (t : ℝ) : ℝ) : ℂ) * D.vertex (ext i) := rfl

@[simp] theorem norm_radialAccess (D : PlanarDrawing G ext) (i : Fin s)
    (t : unitInterval) : ‖D.radialAccess i t‖ = 1 + (t : ℝ) := by
  rw [radialAccess_apply, norm_mul, D.external_on_circle, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  linarith [t.property.1]

theorem radialAccess_disjoint (D : PlanarDrawing G ext) {i j : Fin s}
    (hij : i ≠ j) :
    Disjoint (Set.range (D.radialAccess i)) (Set.range (D.radialAccess j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t, rfl⟩ ⟨u, hu⟩
  have hnorm := congrArg norm hu
  rw [D.norm_radialAccess, D.norm_radialAccess] at hnorm
  have htu : u = t := Subtype.ext (by linarith)
  subst u
  have hc : (((1 + (t : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    linarith [t.property.1]
  exact hij (D.external_injective (D.vertex_injective (mul_left_cancel₀ hc hu).symm))

/-- Every disk drawing has actual ordered, disjoint exterior access on the same
graph, using the surrounding circle of radius two. -/
def orderedExteriorAccess (D : PlanarDrawing G ext) :
    OrderedExteriorAccess D.toPlaneDrawing ext where
  external_injective := D.external_injective
  radius := 2
  radius_pos := by norm_num
  vertex_bound := fun v => (D.vertex_in_disk v).trans (by norm_num)
  edge_bound := fun e t => (D.edge_in_disk e t).trans (by norm_num)
  angle := D.angle
  angle_pos := D.angle_pos
  angle_lt_one := D.angle_lt_one
  angle_strictMono := D.angle_strictMono
  access := D.radialAccess
  access_bound := fun i t => by
    change ‖D.radialAccess i t‖ ≤ (2 : ℝ)
    rw [D.norm_radialAccess]
    linarith [t.property.2]
  access_disjoint := fun _ _ hij => D.radialAccess_disjoint hij
  access_meets_edge_only_at_start := by
    intro i t e u h
    have hn := congrArg norm h
    change ‖D.radialAccess i t‖ = ‖D.edge e u‖ at hn
    rw [D.norm_radialAccess] at hn
    apply Subtype.ext
    change (t : ℝ) = 0
    linarith [D.edge_in_disk e u, t.property.1]

end PlanarDrawing
end
end MatchgateWidth
