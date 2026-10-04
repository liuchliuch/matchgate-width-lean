import MatchgateWidth.AllLeftConnectorPlacement

/-! # Derived round-carrier avoidance for all geometric stages -/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- All local connector banks remain well inside the surrounding unit circle. -/
theorem norm_lt_three_quarters_of_primitive_disk (v : Fin a ⊕ Fin b) {z : ℂ}
    (hz : dist z (K.ordered.primitiveCenter v) ≤ 3*K.collars.radius) : ‖z‖ < (3:ℝ)/4 := by
  have hn : ‖z‖ ≤ dist z (K.ordered.primitiveCenter v) + ‖K.ordered.primitiveCenter v‖ := by
    simpa only [dist_eq_norm,add_comm] using norm_le_insert' z (K.ordered.primitiveCenter v)
  linarith [K.primitive_bound v,K.collars.small]

/-- Radius-r/4 graph carriers of every primitive occurrence. -/
def innerDisks : Set ℂ := ⋃ v : Fin a ⊕ Fin b,
  Metric.closedBall (K.ordered.primitiveCenter v) (K.collars.radius/4)

/-- A path in its own radius-three disk misses every other inserted disk. -/
theorem local_path_avoids_other_inner {x y : ℂ} (P : Path x y)
    (v : Fin a ⊕ Fin b) (hP : ∀ u, dist (P u) (K.ordered.primitiveCenter v) ≤ 3*K.collars.radius)
    (w : Fin a ⊕ Fin b) (hvw : v ≠ w) :
    Disjoint (Set.range P) (Metric.closedBall (K.ordered.primitiveCenter w) (K.collars.radius/4)) :=
  (K.primitive_three_disjoint hvw).mono
    (by rintro z ⟨u,rfl⟩; exact hP u)
    (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))

theorem leftConnector_inner_only_start (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    {ε : ℝ} (BL : ∀ v, K.LeftBank L hL ε v) (q) (u : unitInterval)
    (hu : K.leftConnector L hL BL q u ∈ K.innerDisks) : u = 0 := by
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hu
  by_cases he : v = Sum.inl q.1
  · subst v
    exact (K.leftAngles q.1).roundCollarBank_inner_only_start _ _ _ _ (BL q.1) q.2 u hv
  · exact (Set.disjoint_left.mp (K.local_path_avoids_other_inner
      (K.leftConnector L hL BL q) (Sum.inl q.1) (K.leftConnector_bound L hL BL q) v (Ne.symm he))
        ⟨u,rfl⟩ hv).elim

theorem rightConnector_inner_only_start (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn)
    {ε : ℝ} (BR : ∀ v, K.RightBank R hR ε v) (q) (u : unitInterval)
    (hu : K.rightConnector R hR BR q u ∈ K.innerDisks) : u = 0 := by
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hu
  by_cases he : v = Sum.inr q.1
  · subst v
    exact (K.rightAngles q.1).roundCollarBank_inner_only_start _ _ _ _ (BR q.1) q.2 u hv
  · exact (Set.disjoint_left.mp (K.local_path_avoids_other_inner
      (K.rightConnector R hR BR q) (Sum.inr q.1) (K.rightConnector_bound R hR BR q) v (Ne.symm he))
        ⟨u,rfl⟩ hv).elim

theorem leftCarrier_subset_inner (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) (v : Fin a) :
    (K.leftCarriers L hL).carrier v ⊆ K.innerDisks := by
  intro z hz
  apply Set.mem_iUnion.mpr
  refine ⟨Sum.inl v,?_⟩
  simpa only [leftCarriers,LocalMatchingGraphFamily.insertedCarriers,K.norm_leftFactor] using hz

theorem rightCarrier_subset_inner (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) (v : Fin b) :
    (K.rightCarriers R hR).carrier v ⊆ K.innerDisks := by
  intro z hz
  apply Set.mem_iUnion.mpr
  refine ⟨Sum.inr v,?_⟩
  simpa only [rightCarriers,LocalMatchingGraphFamily.insertedCarriers,K.norm_rightFactor] using hz

/-- Every middle ribbon avoids every actual inserted local graph carrier. -/
theorem laneSupport_avoids_inner {ε δ : ℝ} (e : Fin c ⊕ Fin n)
    (hW : (K.route e).Width ε) (hδ : |δ| < ε) :
    Disjoint ((K.route e).laneSupport δ) K.innerDisks := by
  apply Set.disjoint_left.mpr
  intro z hz hi
  have hcarrier := (K.route e).laneSupport_subset_carriers hW hδ hz
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hcarrier
  have hb := (K.carrier_geometry e z (K.route_carrier_subset e j hj)).2
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hi
  have hh := hb (Sum.inl v)
  change dist z (K.ordered.primitiveCenter v) ≤ K.collars.radius/4 at hv
  change K.collars.radius < dist z (K.ordered.primitiveCenter v) at hh
  linarith [K.collars.positive]

namespace OuterAccessBank
variable {K} {ε : ℝ} (B : K.OuterAccessBank (t := t) ε)

theorem norm_cap (q : Fin (n*t)) : ‖K.boundaryCap ε q‖ = B.radius q := by
  rw [B.cap_eq,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (B.radius_pos q)]

theorem norm_gt_three_quarters (q : Fin (n*t)) (u : unitInterval) :
    (3:ℝ)/4 < ‖B.path q u‖ := by
  have hh := B.norm_lower q u
  rw [B.norm_cap] at hh
  exact (B.radius_gt_three_quarters q).trans_le hh

theorem avoids_inner (q : Fin (n*t)) : Disjoint (Set.range (B.path q)) K.innerDisks := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,rfl⟩ hi
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hi
  have hn := K.norm_lt_three_quarters_of_primitive_disk v
    (le_trans hv (by linarith [K.collars.positive]))
  exact (not_lt_of_ge (B.norm_gt_three_quarters q u).le) hn

theorem disjoint_leftConnector (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    (BL : ∀ v, K.LeftBank L hL ε v) (q : Fin (n*t)) (s) :
    Disjoint (Set.range (B.path q)) (Set.range (K.leftConnector L hL BL s)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,rfl⟩ ⟨v,hv⟩
  have hn := K.norm_lt_three_quarters_of_primitive_disk (Sum.inl s.1)
    (K.leftConnector_bound L hL BL s v)
  rw [hv] at hn
  exact (not_lt_of_ge (B.norm_gt_three_quarters q u).le) hn

theorem disjoint_rightConnector (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn)
    (BR : ∀ v, K.RightBank R hR ε v) (q : Fin (n*t)) (s) :
    Disjoint (Set.range (B.path q)) (Set.range (K.rightConnector R hR BR s)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,rfl⟩ ⟨v,hv⟩
  have hn := K.norm_lt_three_quarters_of_primitive_disk (Sum.inr s.1)
    (K.rightConnector_bound R hR BR s v)
  rw [hv] at hn
  exact (not_lt_of_ge (B.norm_gt_three_quarters q u).le) hn

end OuterAccessBank
end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
