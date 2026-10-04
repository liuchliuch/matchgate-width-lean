import MatchgateWidth.ConnectorZeroSeparation
import MatchgateWidth.IndexedDrawingCollars

/-! # Nonincident local-connector separation derived from actual source collars

These theorems apply directly to the source drawing's trimmed polygonal
corridors. Cut-radius avoidance supplies the radial bound, and actual route
simplicity or cross-edge disjointness excludes the connector's own cutpoint.
Consequently no zero-stage disjointness assumption is needed.
-/
namespace MatchgateWidth
noncomputable section
open Set
namespace PlanarDrawing.IndexedRoutes.Collars
variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}
    {D : PlanarDrawing G ext} {Q : D.IndexedRoutes} (C : Q.Collars)

private theorem sourceCut_mem_support (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E) :
    (Q e).radialSourceCut δ ∈ C.support δ hδ hδmax e := by
  apply Set.mem_iUnion.mpr
  refine ⟨(Q e).firstEdge,?_⟩
  exact ((C.trimRoute δ hδ hδmax e).source_mem_segment_iff_index_zero _).mpr rfl

private theorem targetCut_mem_support (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E) :
    (Q e).radialTargetCut δ ∈ C.support δ hδ hδmax e := by
  apply Set.mem_iUnion.mpr
  refine ⟨(Q e).lastEdge,?_⟩
  apply ((C.trimRoute δ hδ hδmax e).target_mem_segment_iff_last _).mpr
  simp only [IndexedSimplePolygonalRoute.lastEdge_val]
  change (Q e).edgeCount - 1 + 1 = (Q e).edgeCount
  have h := (Q e).positive
  omega

/-- An outgoing zero-width local connector misses every corridor segment
except the first segment of its own original source edge. -/
theorem source_connector_piece_disjoint {n r : ℕ} {p : Fin n → ℂ}
    (A : OrderedRayAngles p) (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (α : Fin (n*r) → ℝ) (R S : ℝ) (hR : 0 < R) (hRS : R < S)
    (hS : ∀ i, S ≤ A.radius i) (q : Fin (n*r))
    (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e f : E)
    (i : Fin (Q f).edgeCount)
    (hcut : D.vertex (G.left e) + p (finProdFinEquiv.symm q).1 = (Q e).radialSourceCut δ)
    (haway : e ≠ f ∨ i.val ≠ 0) :
    Disjoint (Set.range (A.localBlockConnector (D.vertex (G.left e)) w d α R S 0 q))
      (segment ℝ ((C.trimRoute δ hδ hδmax f).vertex i.castSucc)
        ((C.trimRoute δ hδ hδmax f).vertex i.succ)) := by
  have hnorm : ‖p (finProdFinEquiv.symm q).1‖ = δ := by
    have h := (Q e).radialSourceCut_dist δ hδ.le
    rw [← hcut,dist_eq_norm,add_sub_cancel_left] at h
    exact h
  apply A.localBlockConnector_zero_disjoint_of_outside _ w d α R S hR hRS hS q
  · intro z hz
    rw [hnorm]
    exact C.trimRoute_segment_outside δ hδ hδmax (G.left e) f i hz
  · rw [hcut]
    intro hz
    by_cases hef : e = f
    · subst f
      exact haway.resolve_left (not_ne_iff.mpr rfl)
        (((C.trimRoute δ hδ hδmax e).source_mem_segment_iff_index_zero i).mp hz)
    · exact Set.disjoint_left.mp (C.supports_disjoint δ hδ hδmax hef)
        (C.sourceCut_mem_support δ hδ hδmax e) (Set.mem_iUnion.mpr ⟨i,hz⟩)

/-- An incoming zero-width local connector misses every corridor segment
except the last segment of its own original target edge. -/
theorem target_connector_piece_disjoint {n r : ℕ} {p : Fin n → ℂ}
    (A : OrderedRayAngles p) (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (α : Fin (n*r) → ℝ) (R S : ℝ) (hR : 0 < R) (hRS : R < S)
    (hS : ∀ i, S ≤ A.radius i) (q : Fin (n*r))
    (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e f : E)
    (i : Fin (Q f).edgeCount)
    (hcut : D.vertex (G.right e) + p (finProdFinEquiv.symm q).1 = (Q e).radialTargetCut δ)
    (haway : e ≠ f ∨ i.val+1 ≠ (Q f).edgeCount) :
    Disjoint (Set.range (A.localBlockConnector (D.vertex (G.right e)) w d α R S 0 q))
      (segment ℝ ((C.trimRoute δ hδ hδmax f).vertex i.castSucc)
        ((C.trimRoute δ hδ hδmax f).vertex i.succ)) := by
  have hnorm : ‖p (finProdFinEquiv.symm q).1‖ = δ := by
    have h := (Q e).radialTargetCut_dist δ hδ.le
    rw [← hcut,dist_eq_norm,add_sub_cancel_left] at h
    exact h
  apply A.localBlockConnector_zero_disjoint_of_outside _ w d α R S hR hRS hS q
  · intro z hz
    rw [hnorm]
    exact C.trimRoute_segment_outside δ hδ hδmax (G.right e) f i hz
  · rw [hcut]
    intro hz
    by_cases hef : e = f
    · subst f
      exact haway.resolve_left (not_ne_iff.mpr rfl)
        (((C.trimRoute δ hδ hδmax e).target_mem_segment_iff_last i).mp hz)
    · exact Set.disjoint_left.mp (C.supports_disjoint δ hδ hδmax hef)
        (C.targetCut_mem_support δ hδ hδmax e) (Set.mem_iUnion.mpr ⟨i,hz⟩)

end PlanarDrawing.IndexedRoutes.Collars
end
end MatchgateWidth
