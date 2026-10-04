import MatchgateWidth.AllLeftThreePieceComponents
import MatchgateWidth.ThreePieceRoutingReindex
import MatchgateWidth.BridgeBoundaryExteriorAccess
import MatchgateWidth.AllLeftLiftingFromRouting

/-! # Literal two-family drawings and their derived stage carrier conditions -/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

def leftPlane (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :=
  PlaneDrawing.sigmaDrawing (K.leftDrawings L hL) (K.leftCarriers L hL)

def rightPlane (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :=
  PlaneDrawing.sigmaDrawing (K.rightDrawings R hR) (K.rightCarriers R hR)

def familyCarriers (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) :=
  PlaneDrawing.bipartiteCarriers (K.leftDrawings L hL) (K.rightDrawings R hR)
    (K.leftCarriers L hL) (K.rightCarriers R hR) (K.carriers_cross L R hL hR)

theorem leftUnion_subset_inner (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :
    (⋃ v, (K.leftCarriers L hL).carrier v) ⊆ K.innerDisks :=
  Set.iUnion_subset (K.leftCarrier_subset_inner L hL)

theorem rightUnion_subset_inner (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :
    (⋃ v, (K.rightCarriers R hR).carrier v) ⊆ K.innerDisks :=
  Set.iUnion_subset (K.rightCarrier_subset_inner R hR)

theorem leftConnector_meets_left (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    {ε : ℝ} (BL : ∀ v, K.LeftBank L hL ε v) (q) :
    Set.range (K.leftConnector L hL BL q) ∩ (⋃ v, (K.leftCarriers L hL).carrier v) ⊆
      {(K.leftDrawings L hL q.1).vertex (L.external q.1 q.2)} := by
  rintro z ⟨⟨u,rfl⟩,hz⟩
  have hu := K.leftConnector_inner_only_start L hL BL q u (K.leftUnion_subset_inner L hL hz)
  rw [hu]
  exact (K.leftConnector L hL BL q).source

theorem rightConnector_meets_right (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn)
    {ε : ℝ} (BR : ∀ v, K.RightBank R hR ε v) (q) :
    Set.range (K.rightConnector R hR BR q) ∩ (⋃ v, (K.rightCarriers R hR).carrier v) ⊆
      {(K.rightDrawings R hR q.1).vertex (R.external q.1 q.2)} := by
  rintro z ⟨⟨u,rfl⟩,hz⟩
  have hu := K.rightConnector_inner_only_start R hR BR q u (K.rightUnion_subset_inner R hR hz)
  rw [hu]
  exact (K.rightConnector R hR BR q).source

theorem leftConnector_avoids_right (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ} (BL : ∀ v, K.LeftBank L hL ε v) (q) :
    Disjoint (Set.range (K.leftConnector L hL BL q)) (⋃ v, (K.rightCarriers R hR).carrier v) := by
  apply Set.disjoint_left.mpr
  rintro z hz hu
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hu
  have hd := K.local_path_avoids_other_inner (K.leftConnector L hL BL q) (Sum.inl q.1)
    (K.leftConnector_bound L hL BL q) (Sum.inr v) (by simp)
  apply Set.disjoint_left.mp hd hz
  simpa only [rightCarriers,LocalMatchingGraphFamily.insertedCarriers,K.norm_rightFactor] using hv

theorem rightConnector_avoids_left (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ} (BR : ∀ v, K.RightBank R hR ε v) (q) :
    Disjoint (Set.range (K.rightConnector R hR BR q)) (⋃ v, (K.leftCarriers L hL).carrier v) := by
  apply Set.disjoint_left.mpr
  rintro z hz hu
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hu
  have hd := K.local_path_avoids_other_inner (K.rightConnector R hR BR q) (Sum.inr q.1)
    (K.rightConnector_bound R hR BR q) (Sum.inl v) (by simp)
  apply Set.disjoint_left.mp hd hz
  simpa only [leftCarriers,LocalMatchingGraphFamily.insertedCarriers,K.norm_leftFactor] using hv

theorem norm_le_two_of_inner {z : ℂ} (hz : z ∈ K.innerDisks) : ‖z‖ ≤ 2 := by
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
  have hh := K.norm_lt_three_quarters_of_primitive_disk v
    (le_trans hv (by linarith [K.collars.positive]))
  linarith

theorem allRight_norm_le_two (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (B : K.OuterAccessBank (t := t) ε)
    (w : (Fin c ⊕ Fin n) × Fin t) {z : ℂ}
    (hz : z ∈ Set.range (K.allRight R hR BR B w)) : ‖z‖ ≤ 2 := by
  rcases w with ⟨e,k⟩
  cases e with
  | inl e =>
    rw [K.allRight_range_internal] at hz
    obtain ⟨u,rfl⟩ := hz
    have hh := K.norm_lt_three_quarters_of_primitive_disk (Sum.inr (I.rightWireEquiv (e,k)).1)
      (K.rightConnector_bound R hR BR (I.rightWireEquiv (e,k)) u)
    linarith
  | inr p =>
    rw [K.allRight_range_boundary] at hz
    obtain ⟨u,rfl⟩ := hz
    exact B.bound _ u

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
