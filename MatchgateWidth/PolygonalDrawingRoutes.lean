import MatchgateWidth.PolygonalGraphReplacement

/-! # Indexed simple routes inside the exact traces of polygonal drawings -/
namespace MatchgateWidth
noncomputable section
open Set

/-- Enlarging a carrier preserves finite polygonal reachability. -/
theorem PolygonallyJoinedIn.mono {U W : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) (hUW : U⊆W) : PolygonallyJoinedIn W x y :=
  Relation.ReflTransGen.mono (r := fun a b => segment ℝ a b⊆U)
    (p := fun a b => segment ℝ a b⊆W) (fun _ _ hseg => hseg.trans hUW) _ _ h

/-- A finite polygonal path is polygonally connected inside its exact image;
there is no openness or neighborhood premise here. -/
theorem IsPolygonalPath.polygonallyJoinedIn_range {x y : ℂ} {p : Path x y}
    (h : IsPolygonalPath p) : PolygonallyJoinedIn (Set.range p) x y := by
  induction h with
  | segment x y =>
    exact Relation.ReflTransGen.single (by rw [Path.range_segment])
  | @trans x y z p q hp hq ihp ihq =>
    rw [Path.trans_range]
    exact (ihp.mono Set.subset_union_left).trans (ihq.mono Set.subset_union_right)

/-- The route is chosen in the original polygonal trace itself. -/
theorem IsPolygonalPath.exists_indexed_route_in_range {x y : ℂ} {p : Path x y}
    (h : IsPolygonalPath p) (hne : x≠y) :
    Nonempty (IndexedSimplePolygonalRoute (Set.range p) x y) :=
  h.polygonallyJoinedIn_range.exists_indexed_simple_route hne

namespace PlanarDrawing
variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- One indexed simple polygonal route for every original edge; its segments
are constrained to that original edge's exact geometric image. -/
abbrev IndexedRoutes (D : PlanarDrawing G ext) :=
  ∀ e, IndexedSimplePolygonalRoute (Set.range (D.edge e))
    (D.vertex (G.left e)) (D.vertex (G.right e))

/-- Actual polygonal drawings supply indexed simple route data without any
additional route-existence assumption. -/
theorem exists_indexed_routes (D : PlanarDrawing G ext)
    (hp : ∀ e, IsPolygonalPath (D.edgePath e)) : Nonempty D.IndexedRoutes := by
  classical
  exact ⟨fun e => Classical.choice ((hp e).exists_indexed_route_in_range
    (fun he => G.loopless e (D.vertex_injective he)))⟩

end PlanarDrawing
end
end MatchgateWidth
