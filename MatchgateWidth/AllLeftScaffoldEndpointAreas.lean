import MatchgateWidth.AllLeftTransverseScaffold
import MatchgateWidth.PolygonalCorridorEndpointAreas

/-! # Signed endpoint sections of the derived all-left transverse scaffold -/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n : ℕ} {I : AllLeftGadget S a b c n}
variable (K : I.TransverseScaffold)

private theorem first_cut_bound (e : Fin c ⊕ Fin n) :
    3*K.cutRadius < ‖(K.indexed e).vertex (K.indexed e).firstEdge.succ-
      (K.indexed e).vertex (K.indexed e).firstEdge.castSucc‖ := by
  simp only [(K.indexed e).firstEdge_castSucc,(K.indexed e).source]
  have hh := (K.collars.lengths e).1
  dsimp only [cutRadius]
  linarith [K.collars.positive]

private theorem last_cut_bound (e : Fin c ⊕ Fin n) :
    3*K.cutRadius < ‖(K.indexed e).vertex (K.indexed e).lastEdge.succ-
      (K.indexed e).vertex (K.indexed e).lastEdge.castSucc‖ := by
  simp only [(K.indexed e).lastEdge_succ,(K.indexed e).target]
  have hh := (K.collars.lengths e).2
  dsimp only [cutRadius]
  linarith [K.collars.positive]

/-- Source endpoint sections have the positive sign required by a left
connector bank, derived from the actual first corridor edge. -/
theorem source_area_positive (e : Fin c ⊕ Fin n) :
    0<orientedArea ((K.indexed e).radialSourceCut K.cutRadius-
      K.ordered.drawing.vertex (I.graph.left e)) ((K.route e).transverse 0) :=
  (K.indexed e).trimmed_source_area_positive K.cutRadius K.cutRadius_pos
    (K.first_cut_bound e) (K.last_cut_bound e) (K.route e) (K.route_vertex e)

/-- Reversed target endpoint sections have the negative sign required by a
right connector bank, with no independent angle-sign hypothesis. -/
theorem target_area_negative (e : Fin c ⊕ Fin n) :
    orientedArea ((K.indexed e).radialTargetCut K.cutRadius-
      K.ordered.drawing.vertex (I.graph.right e))
      ((K.route e).transverse (Fin.last (K.indexed e).edgeCount))<0 :=
  (K.indexed e).trimmed_target_area_negative K.cutRadius K.cutRadius_pos
    (K.first_cut_bound e) (K.last_cut_bound e) (K.route e) (K.route_vertex e)

/-- At an external boundary port, the global position vector has positive
area against the last transverse section, exactly as needed for outward
boundary connector banks. -/
theorem boundary_area_positive (p : Fin n) :
    0<orientedArea
      (((1-K.cutRadius:ℝ):ℂ)*boundaryPoint (K.ordered.drawing.angle p))
      ((K.route (Sum.inr p)).transverse (Fin.last (K.indexed (Sum.inr p)).edgeCount)) := by
  have hh := K.target_area_negative (Sum.inr p)
  have hcut := K.ordered.boundary_radialTargetCut K.indexed p (K.boundary_germ p)
    K.cutRadius K.cutRadius_pos
  have hv : K.ordered.drawing.vertex (I.graph.right (Sum.inr p)) =
      boundaryPoint (K.ordered.drawing.angle p) := K.ordered.drawing.external_vertex p
  rw [hcut] at hh
  conv at hh =>
    lhs
    arg 1
    rw [hv]
  have hlt : K.cutRadius<1 := by
    dsimp only [cutRadius]
    linarith [K.collars.small]
  exact radial_target_global_area_positive K.cutRadius_pos hlt hh

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
