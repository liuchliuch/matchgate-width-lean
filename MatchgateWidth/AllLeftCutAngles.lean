import MatchgateWidth.IndexedRouteGerms
import MatchgateWidth.IndexedPolygonalRadialTrimming
import MatchgateWidth.AllLeftLocalPlacement
import MatchgateWidth.OuterBoundaryLaneAccess

/-! # Actual ordered angular data for the source collar cuts

The ordered ray lists are derived from indexed routes inside the original
simple edge traces. Positive tangent agreement and positive radial scaling
retain the marked native port order, including empty port lists.
-/
namespace MatchgateWidth
noncomputable section

/-- Any positive rescaling of every actual prescribed germ vector retains its
marked order. The factors may be different at every port. -/
theorem positivePortOrder_ordered_positive_multiples {m : ℕ} {c : ℂ}
    {arc : Fin m → unitInterval → ℂ} (P : LabelledInstance.PositivePortOrder c arc)
    (q : Fin m → ℂ)
    (hq : ∀ i, ∃ κ : ℝ, 0 < κ ∧
      q i = κ • (P.speed i • (P.rotation * twoCenterSquare (P.time i)))) :
    Nonempty (OrderedRayAngles q) := by
  classical
  choose κ hκ hq using hq
  obtain ⟨A⟩ := positivePortOrder_orderedRayAngles P
  have he : q = fun i => κ i • (P.speed i • (P.rotation * twoCenterSquare (P.time i))) := funext hq
  rw [he]
  exact ⟨A.positiveScale κ hκ⟩

namespace IndexedSimplePolygonalRoute
variable {x y v : ℂ} {p : Path x y}

/-- A source collar cut has the positive direction of the true source germ. -/
theorem radialSourceCut_positive_germ (R : IndexedSimplePolygonalRoute (Set.range p) x y)
    (hi : Function.Injective p) {τ : unitInterval} (hτ : 0 < τ)
    (hg : ∀ u : unitInterval, u ≤ τ → p u = x + (u:ℝ) • v)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ R.radialSourceCut δ - x = κ • v := by
  obtain ⟨κ,hκ,hdir⟩ := R.first_tangent_positive hi hτ hg
  have hn : 0 < ‖R.vertex R.firstEdge.succ-x‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    simpa only [R.firstEdge_castSucc,R.source] using (R.nonzero R.firstEdge).symm
  refine ⟨(δ/‖R.vertex R.firstEdge.succ-x‖)*κ,mul_pos (div_pos hδ hn) hκ,?_⟩
  simp only [radialSourceCut,radialSegmentCut,R.firstEdge_castSucc,R.source,add_sub_cancel_left]
  rw [hdir,smul_smul]

/-- A target collar cut has the positive direction of the true outgoing germ. -/
theorem radialTargetCut_positive_germ (R : IndexedSimplePolygonalRoute (Set.range p) x y)
    (hi : Function.Injective p) {τ : unitInterval} (hτ : 0 < τ)
    (hg : ∀ u : unitInterval, u ≤ τ → p.symm u = y + (u:ℝ) • v)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ R.radialTargetCut δ - y = κ • v := by
  obtain ⟨κ,hκ,hdir⟩ := R.last_reverse_tangent_positive hi hτ hg
  have hn : 0 < ‖R.vertex R.lastEdge.castSucc-y‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    simpa only [R.lastEdge_succ,R.target] using R.nonzero R.lastEdge
  refine ⟨(δ/‖R.vertex R.lastEdge.castSucc-y‖)*κ,mul_pos (div_pos hδ hn) hκ,?_⟩
  simp only [radialTargetCut,radialSegmentCut,R.lastEdge_succ,R.target,add_sub_cancel_left]
  rw [hdir,smul_smul]

end IndexedSimplePolygonalRoute

namespace AllLeftGadget.OrderedPlanar
variable {S : LabelledShape} {a b c n : ℕ} {I : AllLeftGadget S a b c n}
    (Q : I.OrderedPlanar) (R : Q.drawing.IndexedRoutes)

/-- Exact indexed source-cut vectors at a left occurrence. -/
def leftCutVector (δ : ℝ) (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v))) : ℂ :=
  (R (I.leftIncidence ⟨v,i⟩)).radialSourceCut δ - Q.primitiveCenter (Sum.inl v)

/-- Exact indexed target-cut vectors in the outward right-occurrence frame. -/
def rightCutVector (δ : ℝ) (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v))) : ℂ :=
  (R (Sum.inl (I.rightIncidence ⟨v,i⟩))).radialTargetCut δ - Q.primitiveCenter (Sum.inr v)

/-- Original positive left port order yields actual ordered source cut angles. -/
theorem leftCutVector_ordered (δ : ℝ) (hδ : 0 < δ) (v : Fin a) :
    Nonempty (OrderedRayAngles (Q.leftCutVector R δ v)) := by
  apply positivePortOrder_ordered_positive_multiples (Q.leftOrder v)
  intro i
  have hsrc : Q.drawing.vertex (I.graph.left (I.leftIncidence ⟨v,i⟩)) =
      Q.primitiveCenter (Sum.inl v) := by
    simp [AllLeftGadget.graph,primitiveCenter]
  have hg := (R (I.leftIncidence ⟨v,i⟩)).radialSourceCut_positive_germ
    (p := Q.drawing.edgePath (I.leftIncidence ⟨v,i⟩))
    (v := (Q.leftOrder v).speed i • ((Q.leftOrder v).rotation * twoCenterSquare ((Q.leftOrder v).time i)))
    (Q.drawing.edge_injective _) (Q.leftOrder v).radius_pos
    (fun u hu => by
      change Q.drawing.edge (I.leftIncidence ⟨v,i⟩) u = _
      rw [hsrc]
      exact (Q.leftOrder v).germ i u hu) δ hδ
  simpa only [PlanarDrawing.edgePath,leftCutVector,hsrc] using hg

/-- Original positive right port order yields actual ordered target cut angles. -/
theorem rightCutVector_ordered (δ : ℝ) (hδ : 0 < δ) (v : Fin b) :
    Nonempty (OrderedRayAngles (Q.rightCutVector R δ v)) := by
  apply positivePortOrder_ordered_positive_multiples (Q.rightOrder v)
  intro i
  have htgt : Q.drawing.vertex (I.graph.right (Sum.inl (I.rightIncidence ⟨v,i⟩))) =
      Q.primitiveCenter (Sum.inr v) := by
    simp [AllLeftGadget.graph,primitiveCenter]
  have hg := (R (Sum.inl (I.rightIncidence ⟨v,i⟩))).radialTargetCut_positive_germ
    (p := Q.drawing.edgePath (Sum.inl (I.rightIncidence ⟨v,i⟩)))
    (v := (Q.rightOrder v).speed i • ((Q.rightOrder v).rotation * twoCenterSquare ((Q.rightOrder v).time i)))
    (Q.drawing.edge_injective _) (Q.rightOrder v).radius_pos
    (fun u hu => by
      change Q.drawing.edge (Sum.inl (I.rightIncidence ⟨v,i⟩))
        (LabelledInstance.reverseParameter u) = _
      rw [htgt]
      exact (Q.rightOrder v).germ i u hu) δ hδ
  simpa only [PlanarDrawing.edgePath,rightCutVector,htgt] using hg

/-- An inward radial boundary germ forces the exact global radial cut point.
This identity pins the global angle to the original first-labelled boundary. -/
theorem boundary_radialTargetCut (p : Fin n)
    (hg : ∃ κ : ℝ, 0 < κ ∧ ∃ τ : unitInterval, 0 < τ ∧
      ∀ u : unitInterval, u ≤ τ →
        Q.drawing.edge (Sum.inr p) (LabelledInstance.reverseParameter u) =
          boundaryPoint (Q.drawing.angle p) +
            (u:ℝ) • (κ • (-boundaryPoint (Q.drawing.angle p))))
    (δ : ℝ) (hδ : 0 < δ) :
    (R (Sum.inr p)).radialTargetCut δ =
      ((1-δ:ℝ):ℂ) * boundaryPoint (Q.drawing.angle p) := by
  obtain ⟨κ,hκ,τ,hτ,hg⟩ := hg
  have htgt : Q.drawing.vertex (I.graph.right (Sum.inr p)) = boundaryPoint (Q.drawing.angle p) := by
    simpa only [AllLeftGadget.graph,Sum.elim_inr] using Q.drawing.external_vertex p
  obtain ⟨μ,hμ,hdir⟩ := (R (Sum.inr p)).radialTargetCut_positive_germ
    (p := Q.drawing.edgePath (Sum.inr p)) (v := κ • (-boundaryPoint (Q.drawing.angle p)))
    (Q.drawing.edge_injective _) hτ
    (fun u hu => by
      change Q.drawing.edge (Sum.inr p) (LabelledInstance.reverseParameter u) = _
      rw [htgt]
      exact hg u hu) δ hδ
  dsimp only [PlanarDrawing.edgePath] at hdir
  simp only [htgt,smul_smul] at hdir
  have hnorm := (R (Sum.inr p)).radialTargetCut_dist δ hδ.le
  simp only [htgt] at hnorm
  rw [dist_eq_norm,hdir,norm_smul,Real.norm_eq_abs,
    abs_of_pos (mul_pos hμ hκ),norm_neg,norm_boundaryPoint,mul_one] at hnorm
  rw [hnorm] at hdir
  have he := eq_add_of_sub_eq hdir
  rw [he,Complex.real_smul]
  push_cast
  ring

end AllLeftGadget.OrderedPlanar
end
end MatchgateWidth
