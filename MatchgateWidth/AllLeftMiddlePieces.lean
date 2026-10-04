import MatchgateWidth.AllLeftTransverseScaffold

/-! # Explicit continuously perturbed middle segment traces of source gadgets -/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- The literal affine segment trace of a semantic physical wire. -/
def middlePiece (e : Fin c ⊕ Fin n) (k : Fin t) (i : Fin (K.indexed e).edgeCount)
    (ε : ℝ) : unitInterval → ℂ :=
  (K.route e).edge (physicalLaneOffset ε e k) i

theorem middlePiece_continuous (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) (ε : ℝ) : Continuous (K.middlePiece e k i ε) :=
  (K.route e).edge_continuous _ _

/-- Continuity is proved for the literal segment formula, not a classically
chosen parametrization of the concatenated whole route. -/
theorem middlePiece_joint_continuous (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) :
    Continuous (fun z : ℝ × unitInterval => K.middlePiece e k i z.1 z.2) := by
  unfold middlePiece TransversePolygonalRoute.edge ribbonArc straightArc ribbonSection
    physicalLaneOffset TransversePolygonalRoute.laneOffset
  fun_prop

theorem middlePiece_continuousAt_zero (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) (u : unitInterval) :
    ContinuousAt (fun z : ℝ × unitInterval => K.middlePiece e k i z.1 z.2) (0,u) :=
  (K.middlePiece_joint_continuous e k i).continuousAt

@[simp] theorem middlePiece_zero (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) :
    K.middlePiece e k i 0 = straightArc ((K.route e).vertex i.castSucc) ((K.route e).vertex i.succ) := by
  simp [middlePiece,TransversePolygonalRoute.edge,ribbonArc,ribbonSection,
    physicalLaneOffset,TransversePolygonalRoute.laneOffset]

theorem middlePiece_zero_range (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) :
    Set.range (K.middlePiece e k i 0) =
      segment ℝ ((K.collars.trimRoute (2*K.collars.radius) (by linarith [K.collars.positive])
        (by linarith [K.collars.positive]) e).vertex i.castSucc)
        ((K.collars.trimRoute (2*K.collars.radius) (by linarith [K.collars.positive])
        (by linarith [K.collars.positive]) e).vertex i.succ) := by
  rw [K.middlePiece_zero,range_straightArc,K.route_vertex]

/-- Every sufficiently narrow actual middle piece stays in its source edge's
constructed open corridor. -/
theorem middlePiece_subset_carrier {ε : ℝ} (hε : 0 < ε)
    (hW : ∀ e, (K.route e).Width ε) (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) :
    Set.range (K.middlePiece e k i ε) ⊆ K.openCarrier e :=
  ((hW e (physicalLaneOffset ε e k) (physicalLaneOffset_bounds hε e k).2 i).2.2).trans
    (K.route_carrier_subset e i)

/-- Fixed inner-disk avoidance handles the whole angular interpolation head
of every local connector, uniformly across all incident and nonincident pieces. -/
theorem middlePiece_outside_vertex {ε : ℝ} (hε : 0 < ε)
    (hW : ∀ e, (K.route e).Width ε) (e : Fin c ⊕ Fin n) (k : Fin t)
    (i : Fin (K.indexed e).edgeCount) (v : (Fin a ⊕ Fin b) ⊕ Fin n) :
    Disjoint (Set.range (K.middlePiece e k i ε))
      (Metric.closedBall (K.ordered.drawing.vertex v) K.collars.radius) := by
  apply Set.disjoint_left.mpr
  intro z hz hball
  have hout := (K.carrier_geometry e z (K.middlePiece_subset_carrier hε hW e k i hz)).2 v
  exact (not_le_of_gt hout) hball

/-- The exact union consumed by a whole wire's path-range theorem. -/
theorem iUnion_middlePiece (e : Fin c ⊕ Fin n) (k : Fin t) (ε : ℝ) :
    (⋃ i, Set.range (K.middlePiece e k i ε)) =
      (K.route e).laneSupport (physicalLaneOffset ε e k) := rfl

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
